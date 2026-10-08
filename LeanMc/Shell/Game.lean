import LeanMc.FFI
import LeanMc.Core.World
import LeanMc.Core.Mesh
import LeanMc.Core.Generated
import LeanMc.Shell.Atlas

/-!
# The game shell

Everything that talks to the outside world: the frame loop, input, chunk
streaming and drawing. It decides *when* to load, mesh, tick and draw, but
*what* a chunk contains, *which* faces it shows and *how* the player moves all
come from `LeanMc.Core`.

This module is unverified. Its floating point is confined to the view
direction and to turning exact positions into small numbers for the renderer.
-/

namespace LeanMc.Shell

open FFI

/-- How far chunks are kept loaded around the player, in chunks. -/
def viewRadius : Int := 6
def viewRadiusY : Int := 4

/-- Seconds per simulation tick. -/
def tickSeconds : Float := 1.0 / ticksPerSecond.toFloat

structure Game where
  world : World
  cache : ChunkCache := {}
  /-- Uploaded mesh for each meshed chunk; handle `0` is an empty mesh. -/
  meshes : Std.HashMap ChunkPos UInt32 := {}
  player : Player
  /-- Where the player was one tick ago, so that drawing can blend between ticks. -/
  prevPos : Vec3
  yaw : Float := 0.0
  pitch : Float := 0.0
  /-- Simulated time not yet turned into ticks, in seconds. -/
  tickDebt : Float := 0.0
  captured : Bool := false
  frame : Nat := 0

/-- Offsets of every chunk within view of a centre chunk, nearest first. -/
def chunkOffsets : Array (Int × Int × Int) := Id.run do
  let mut out := #[]
  for i in [0:(2 * viewRadius + 1).toNat] do
    for j in [0:(2 * viewRadiusY + 1).toNat] do
      for k in [0:(2 * viewRadius + 1).toNat] do
        out := out.push ((i : Int) - viewRadius, (j : Int) - viewRadiusY, (k : Int) - viewRadius)
  let dist := fun (o : Int × Int × Int) => o.1 * o.1 + o.2.1 * o.2.1 + o.2.2 * o.2.2
  return out.qsort fun a b => dist a < dist b

namespace Game

/-- Unit vector the player looks along. Yaw `0` faces `-z`. -/
def lookDir (g : Game) : Float × Float × Float :=
  (g.yaw.sin * g.pitch.cos, g.pitch.sin, -(g.yaw.cos * g.pitch.cos))

/--
The eye position to draw from, in fixed-point units: the player's eyes, blended
between the last two ticks by how far into the current tick the frame falls.
-/
def eye (g : Game) : Vec3 :=
  let blend : Int := (max 0.0 (min 1.0 (g.tickDebt / tickSeconds)) * 1024.0).toInt64.toInt
  let mix (a b : Int) : Int := a + (b - a) * blend / 1024
  ⟨mix g.prevPos.x g.player.pos.x,
   mix g.prevPos.y g.player.pos.y + Player.eyeHeight,
   mix g.prevPos.z g.player.pos.z⟩

/-- Solidity as the simulation sees it: the world, read through the chunk cache. -/
def solid (g : Game) (p : BlockPos) : Bool :=
  (g.cache.blockAt g.world p).isSolid

/-- (Re)build and upload the mesh for chunk `c`. -/
def meshChunk (g : Game) (c : ChunkPos) : IO Game := do
  let mut cache := g.cache.load g.world c
  for d in Dir.all do
    cache := cache.load g.world (c.step d)
  let bytes := LeanMc.meshChunk (cache.blockAt g.world) c
  if let some old := g.meshes[c]? then
    unloadMesh old
  let mesh ← uploadMesh bytes
  return { g with cache, meshes := g.meshes.insert c mesh }

/--
Change one block, keeping the cache and the affected meshes up to date. Only
the chunk holding the block and the chunks holding its neighbours can change
(`LeanMc.meshChunk_set`), so only those are rebuilt.
-/
def setBlock (g : Game) (p : BlockPos) (b : Block) : IO Game := do
  let mut g := { g with world := g.world.set p b, cache := g.cache.setBlock p b }
  let mut dirty := [p.chunkPos]
  for d in Dir.all do
    let c := (p.step d).chunkPos
    unless dirty.contains c do
      dirty := c :: dirty
  for c in dirty do
    if g.meshes.contains c then
      g ← g.meshChunk c
  return g

/-- Mesh missing chunks around the player, nearest first, for up to `budgetMs`. -/
def stream (g : Game) (budgetMs : Nat) : IO Game := do
  let centre := g.eye.blockPos.chunkPos
  let start ← IO.monoMsNow
  let mut g := g
  for (dx, dy, dz) in chunkOffsets do
    let c : ChunkPos := ⟨centre.x + dx, centre.y + dy, centre.z + dz⟩
    unless g.meshes.contains c do
      g ← g.meshChunk c
      if (← IO.monoMsNow) - start ≥ budgetMs then
        break
  return g

/-- Drop meshes and cached chunks that are well out of view. -/
def unloadFar (g : Game) : IO Game := do
  let centre := g.eye.blockPos.chunkPos
  let far (c : ChunkPos) (slack : Int) : Bool :=
    (c.x - centre.x).natAbs > viewRadius + slack
      || (c.y - centre.y).natAbs > viewRadiusY + slack
      || (c.z - centre.z).natAbs > viewRadius + slack
  let mut meshes := g.meshes
  for (c, mesh) in g.meshes do
    if far c 1 then
      unloadMesh mesh
      meshes := meshes.erase c
  let mut cache := g.cache
  for (c, _) in g.cache.chunks do
    if far c 2 then
      cache := cache.unload c
  return { g with meshes, cache }

/-- Advance the simulation by one tick. -/
def tick (g : Game) (input : Input) : Game :=
  { g with prevPos := g.player.pos, player := g.player.step g.solid input }

/-- Turn the mouse into a view direction and handle capturing it. -/
def look (g : Game) : IO Game := do
  let mut g := g
  if (← mousePressed Mouse.left) && !g.captured then
    setCursorCaptured true
    g := { g with captured := true }
  if (← keyPressed Key.escape) && g.captured then
    setCursorCaptured false
    g := { g with captured := false }
  if g.captured then
    let pitch := g.pitch - (← mouseDy) * 0.003
    g := { g with yaw := g.yaw + (← mouseDx) * 0.003, pitch := max (-1.55) (min 1.55 pitch) }
  return g

/-- Read the keyboard as the player's intent for a tick. -/
def readInput (g : Game) : IO Input := do
  let axis (pos neg : UInt32) : IO Float := do
    return (if ← keyDown pos then 1.0 else 0.0) - (if ← keyDown neg then 1.0 else 0.0)
  let forward ← axis Key.w Key.s
  let right ← axis Key.d Key.a
  let fast ← keyDown Key.leftControl
  let speed :=
    if g.player.flying then (if fast then Player.fastFlySpeed else Player.flySpeed)
    else (if fast then Player.sprintSpeed else Player.walkSpeed)
  -- Forward is (sin yaw, -cos yaw); right is a quarter turn clockwise from it.
  let (fx, fz) := (g.yaw.sin, -g.yaw.cos)
  let wx := forward * fx - right * fz
  let wz := forward * fz + right * fx
  let len := (wx * wx + wz * wz).sqrt
  let scale := if len > 1.0 then speed.toFloat / len else speed.toFloat
  return {
    wishX := (wx * scale).toInt64.toInt
    wishZ := (wz * scale).toInt64.toInt
    jump := ← keyDown Key.space
    descend := ← keyDown Key.leftShift
    toggleFly := ← keyPressed Key.f
  }

/-- Run as many ticks as the elapsed time calls for. -/
def simulate (g : Game) : IO Game := do
  let mut g := { g with tickDebt := min 0.25 (g.tickDebt + (← frameTime)) }
  let mut input ← g.readInput
  while g.tickDebt ≥ tickSeconds do
    g := { g.tick input with tickDebt := g.tickDebt - tickSeconds }
    -- A key press belongs to one tick only.
    input := { input with toggleFly := false }
  return g

def draw (g : Game) : IO Unit := do
  let eye := g.eye
  let base := eye.blockPos
  -- The eye's offset within its block, which is all the precision the renderer needs.
  let frac (v b : Int) : Float := Float.ofInt (v - b * 65536) / 65536.0
  let (ox, oy, oz) := (frac eye.x base.x, frac eye.y base.y, frac eye.z base.z)
  beginFrame 0x87b5ffff
  let (dx, dy, dz) := g.lookDir
  begin3D 0 0 0 dx dy dz 70.0
  let mut drawn := 0
  for (c, mesh) in g.meshes do
    if mesh != 0 then
      drawn := drawn + 1
      drawMesh mesh
        (Float.ofInt (16 * c.x - base.x) - ox)
        (Float.ofInt (16 * c.y - base.y) - oy)
        (Float.ofInt (16 * c.z - base.z) - oz)
  end3D
  let w ← screenWidth
  let h ← screenHeight
  drawRect (w / 2 - 1) (h / 2 - 8) 2 16 0xffffffff
  drawRect (w / 2 - 8) (h / 2 - 1) 16 2 0xffffffff
  let fps := (1.0 / (← frameTime)).round.toUInt32
  let feet := g.player.pos.blockPos
  let mode := if g.player.flying then "flying" else if g.player.onGround then "on ground" else "in air"
  drawText s!"block {feet.x} {feet.y} {feet.z}   {mode}   {fps} fps" 10 10 20 0xffffffff
  drawText s!"chunks {g.meshes.size} meshed, {drawn} drawn, {g.cache.chunks.size} cached"
    10 34 16 0xffffffff
  unless g.captured do
    drawText "click to capture the mouse   WASD: move   space: jump   ctrl: sprint   F: fly   esc: release"
      10 (h - 26) 16 0xffffffff

end Game

/--
Edits made by the self-test, relative to a block on the ground: a pit, an arch,
and a floating slab that spans a chunk boundary wherever it lands.
-/
def selftestEdits (o : BlockPos) : List (BlockPos × Block) :=
  let rel (dx dy dz : Int) : BlockPos := ⟨o.x + dx, o.y + dy, o.z + dz⟩
  ([-1, 0].flatMap fun dx => [-9, -8].flatMap fun dz => [0, -1, -2, -3, -4, -5].map fun dy =>
      (rel dx dy dz, Block.air))
  ++ [1, 2, 3].flatMap (fun dy => [(rel 3 dy (-9), Block.planks), (rel 6 dy (-9), .planks)])
  ++ [3, 4, 5, 6].map (fun dx => (rel dx 4 (-9), Block.cobble))
  ++ (List.range 18).map (fun (i : Nat) => (rel (Int.ofNat i - 9) 6 (-12), Block.planks))

/-- Options taken from the command line. -/
structure Options where
  /-- Seed of the generated world. -/
  seed : UInt64 := 2026
  /-- Generate the flat test world instead of terrain. -/
  flat : Bool := false
  /-- Block to start in; by default, the generated world's spawn point. -/
  start : Option BlockPos := none
  /-- Run a scripted scene, save a screenshot here and exit. -/
  selftest : Option String := none
  /-- Like `selftest`, but fly across the world first to exercise streaming. -/
  flytest : Option String := none
  /-- Quit after this many frames of normal play, reporting where the player ended up. -/
  frames : Option Nat := none

def Options.parse (opts : Options := {}) : List String → Except String Options
  | [] => pure opts
  | "--selftest" :: path :: rest => parse { opts with selftest := some path } rest
  | "--flytest" :: path :: rest => parse { opts with flytest := some path } rest
  | "--at" :: x :: y :: z :: rest =>
    match x.toInt?, y.toInt?, z.toInt? with
    | some x, some y, some z => parse { opts with start := some ⟨x, y, z⟩ } rest
    | _, _, _ => throw "--at expects three integers"
  | "--seed" :: n :: rest =>
    match n.toNat? with
    | some n => parse { opts with seed := n.toUInt64 } rest
    | none => throw "--seed expects a number"
  | "--flat" :: rest => parse { opts with flat := true } rest
  | "--frames" :: n :: rest =>
    match n.toNat? with
    | some n => parse { opts with frames := some n } rest
    | none => throw "--frames expects a number"
  | arg :: _ => throw s!"unknown argument: {arg}"

def flytestFrames : Nat := 240

/-- The input the scripted tests feed the player on a given frame. -/
def scriptedInput (opts : Options) (g : Game) : Input :=
  if opts.flytest.isSome then
    -- Take off, then fly fast and diagonally while climbing clear of the hills.
    { wishX := 65536, wishZ := -21845, jump := true, toggleFly := g.frame == 0 }
  else
    -- Stand, walk forward, hop once, stop.
    let walking := 40 ≤ g.frame && g.frame < 100
    { wishZ := if walking then -Player.walkSpeed else 0, jump := g.frame == 70 }

partial def loop (g : Game) (opts : Options) : IO Unit := do
  if ← windowShouldClose then return
  let scripted := opts.selftest.isSome || opts.flytest.isSome
  let mut g ← g.look
  -- Scripted runs take exactly one tick per frame so that they are repeatable.
  g ← if scripted then pure { g.tick (scriptedInput opts g) with tickDebt := 0 } else g.simulate
  g ← g.stream (if opts.selftest.isSome then 100000 else 6)
  if opts.selftest.isSome && g.frame == 2 then
    let mut ground := g.player.pos.blockPos
    while !(g.world.get ground).isSolid && ground.y > 0 do
      ground := ground.step .yn
    for (p, b) in selftestEdits ground do
      g ← g.setBlock p b
  if g.frame % 60 == 59 then
    g ← g.unloadFar
  g.draw
  let finish (path : String) : IO Unit := do
    unless path.isEmpty do
      takeScreenshot path
    endFrame
    let p := g.player
    IO.println s!"frame {g.frame}: {g.meshes.size} meshed, {g.cache.chunks.size} cached, \
      feet at {p.pos.x} {p.pos.y} {p.pos.z} units, block {p.pos.blockPos.x} {p.pos.blockPos.y} \
      {p.pos.blockPos.z}, onGround {p.onGround}, flying {p.flying}, \
      inside something solid: {Player.blocked g.solid p.pos}"
  match opts.selftest, opts.flytest with
  | some path, _ => if g.frame == 130 then return ← finish path
  | _, some path => if g.frame == flytestFrames then return ← finish path
  | _, _ => if opts.frames == some g.frame then return ← finish ""
  endFrame
  loop { g with frame := g.frame + 1 } opts

/--
A standing position near the middle of block `b`: raised until it is clear of
anything solid, then lowered onto the ground.
-/
def standNear (world : World) (b : BlockPos) : Vec3 := Id.run do
  let mut pos : Vec3 := ⟨b.x * 65536 + 32768, b.y * 65536, b.z * 65536 + 32768⟩
  let mut tries := 0
  while Player.blocked world.solid pos && tries < 256 do
    pos := pos.add .y 65536
    tries := tries + 1
  return Player.settle world.solid 256 pos

def run (args : List String) : IO UInt32 := do
  let opts ← match Options.parse {} args with
    | .ok opts => pure opts
    | .error message =>
      IO.eprintln message
      IO.eprintln "usage: leanmc [--seed N] [--flat] [--at X Y Z] [--frames N] [--selftest PNG | --flytest PNG]"
      return 2
  let world := if opts.flat then World.new Terrain.flat else Terrain.world opts.seed
  let pos :=
    match opts.start with
    | some b => standNear world b
    | none => if opts.flat then standNear world ⟨7, 12, 14⟩ else Terrain.spawn opts.seed
  initWindow 1280 720 "lean-mc"
  setAtlas Atlas.size.toUInt32 Atlas.size.toUInt32 Atlas.pixels
  loop { world, player := { pos }, prevPos := pos, pitch := -0.35, yaw := 0.15 } opts
  closeWindow
  return 0

end LeanMc.Shell
