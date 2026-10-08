import LeanMc.FFI
import LeanMc.Core.World
import LeanMc.Core.Mesh
import LeanMc.Core.Generated
import LeanMc.Shell.Atlas

/-!
# The game shell

Everything that talks to the outside world: the frame loop, input, chunk
streaming and drawing. It decides *when* to load, mesh and draw, but *what* a
chunk contains and *which* faces it shows come from `LeanMc.Core`.

This module is unverified. Its floating point is confined to the camera.
-/

namespace LeanMc.Shell

open FFI

/-- How far chunks are kept loaded around the camera, in chunks. -/
def viewRadius : Int := 6
def viewRadiusY : Int := 4

/--
A free-flying camera. Its position is a block plus an offset in `[0, 1)`, so
that the distances handed to the renderer are small whatever the coordinates.
-/
structure Camera where
  base : BlockPos
  ox : Float := 0.5
  oy : Float := 0.5
  oz : Float := 0.5
  yaw : Float := 0.0
  pitch : Float := 0.0

namespace Camera

/-- Unit vector the camera looks along. Yaw `0` faces `-z`. -/
def dir (c : Camera) : Float × Float × Float :=
  (c.yaw.sin * c.pitch.cos, c.pitch.sin, -(c.yaw.cos * c.pitch.cos))

def move (c : Camera) (dx dy dz : Float) : Camera :=
  let carry (base : Int) (off : Float) : Int × Float :=
    let whole := off.floor
    (base + whole.toInt64.toInt, off - whole)
  let (x, ox) := carry c.base.x (c.ox + dx)
  let (y, oy) := carry c.base.y (c.oy + dy)
  let (z, oz) := carry c.base.z (c.oz + dz)
  { c with base := ⟨x, y, z⟩, ox, oy, oz }

end Camera

structure Game where
  world : World
  cache : ChunkCache := {}
  /-- Uploaded mesh for each meshed chunk; handle `0` is an empty mesh. -/
  meshes : Std.HashMap ChunkPos UInt32 := {}
  camera : Camera
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

/-- Change one block, keeping the cache and the affected meshes up to date. -/
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

/-- Mesh missing chunks around the camera, nearest first, for up to `budgetMs`. -/
def stream (g : Game) (budgetMs : Nat) : IO Game := do
  let centre := g.camera.base.chunkPos
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
  let centre := g.camera.base.chunkPos
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

def handleInput (g : Game) : IO Game := do
  let mut g := g
  if (← mousePressed Mouse.left) && !g.captured then
    setCursorCaptured true
    g := { g with captured := true }
  if (← keyPressed Key.escape) && g.captured then
    setCursorCaptured false
    g := { g with captured := false }
  let mut cam := g.camera
  if g.captured then
    let pitch := cam.pitch - (← mouseDy) * 0.003
    cam := { cam with yaw := cam.yaw + (← mouseDx) * 0.003, pitch := max (-1.55) (min 1.55 pitch) }
  let speed := if ← keyDown Key.leftControl then 40.0 else 10.0
  let step := (← frameTime) * speed
  let (fx, fz) := (cam.yaw.sin, -cam.yaw.cos)
  if ← keyDown Key.w then cam := cam.move (fx * step) 0 (fz * step)
  if ← keyDown Key.s then cam := cam.move (-fx * step) 0 (-fz * step)
  if ← keyDown Key.d then cam := cam.move (-fz * step) 0 (fx * step)
  if ← keyDown Key.a then cam := cam.move (fz * step) 0 (-fx * step)
  if ← keyDown Key.space then cam := cam.move 0 step 0
  if ← keyDown Key.leftShift then cam := cam.move 0 (-step) 0
  return { g with camera := cam }

def draw (g : Game) : IO Unit := do
  let cam := g.camera
  beginFrame 0x87b5ffff
  let (dx, dy, dz) := cam.dir
  begin3D 0 0 0 dx dy dz 70.0
  let mut drawn := 0
  for (c, mesh) in g.meshes do
    if mesh != 0 then
      drawn := drawn + 1
      drawMesh mesh
        (Float.ofInt (16 * c.x - cam.base.x) - cam.ox)
        (Float.ofInt (16 * c.y - cam.base.y) - cam.oy)
        (Float.ofInt (16 * c.z - cam.base.z) - cam.oz)
  end3D
  let w ← screenWidth
  let h ← screenHeight
  drawRect (w / 2 - 1) (h / 2 - 8) 2 16 0xffffffff
  drawRect (w / 2 - 8) (h / 2 - 1) 16 2 0xffffffff
  let fps := (1.0 / (← frameTime)).round.toUInt32
  drawText s!"block {cam.base.x} {cam.base.y} {cam.base.z}   {fps} fps" 10 10 20 0xffffffff
  drawText s!"chunks {g.meshes.size} meshed, {drawn} drawn, {g.cache.chunks.size} cached"
    10 34 16 0xffffffff
  unless g.captured do
    drawText "click to capture the mouse   WASD space shift: fly   ctrl: fast   esc: release"
      10 (h - 26) 16 0xffffffff

end Game

/--
Edits made by the self-test, relative to a block on the ground: a pit, an arch,
and a floating slab that spans a chunk boundary wherever it lands.
-/
def selftestEdits (o : BlockPos) : List (BlockPos × Block) :=
  let rel (dx dy dz : Int) : BlockPos := ⟨o.x + dx, o.y + dy, o.z + dz⟩
  ([-1, 0].flatMap fun dx => [-6, -5].flatMap fun dz => [0, -1, -2, -3, -4, -5].map fun dy =>
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
  /-- Where the camera starts; by default, just above the ground near the origin. -/
  start : Option BlockPos := none
  /-- Render a scripted scene, save a screenshot here and exit. -/
  selftest : Option String := none
  /-- Like `selftest`, but fly across the world first to exercise streaming. -/
  flytest : Option String := none

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
  | arg :: _ => throw s!"unknown argument: {arg}"

def flytestFrames : Nat := 240

partial def loop (g : Game) (opts : Options) : IO Unit := do
  if ← windowShouldClose then return
  let mut g ← g.handleInput
  if opts.flytest.isSome then
    g := { g with camera := g.camera.move 1.5 0 (-0.5) }
  g ← g.stream (if opts.selftest.isSome then 100000 else 6)
  if opts.selftest.isSome && g.frame == 2 then
    let cam := g.camera.base
    let mut ground : BlockPos := cam
    while !(g.world.get ground).isSolid && ground.y > 0 do
      ground := ground.step .yn
    for (p, b) in selftestEdits ground do
      g ← g.setBlock p b
  if g.frame % 60 == 59 then
    g ← g.unloadFar
  g.draw
  let finish (path : String) : IO Unit := do
    takeScreenshot path
    endFrame
    IO.println s!"frame {g.frame}: {g.meshes.size} meshed, {g.cache.chunks.size} cached, \
      camera at {g.camera.base.x} {g.camera.base.y} {g.camera.base.z}"
  match opts.selftest, opts.flytest with
  | some path, _ => if g.frame == 5 then return ← finish path
  | _, some path => if g.frame == flytestFrames then return ← finish path
  | _, _ => pure ()
  endFrame
  loop { g with frame := g.frame + 1 } opts

def run (args : List String) : IO UInt32 := do
  let opts ← match Options.parse {} args with
    | .ok opts => pure opts
    | .error message =>
      IO.eprintln message
      IO.eprintln "usage: leanmc [--seed N] [--flat] [--at X Y Z] [--selftest PNG | --flytest PNG]"
      return 2
  initWindow 1280 720 "lean-mc"
  setAtlas Atlas.size.toUInt32 Atlas.size.toUInt32 Atlas.pixels
  let world := if opts.flat then World.new Terrain.flat else Terrain.world opts.seed
  let start := opts.start.getD <|
    if opts.flat then ⟨7, Terrain.flatSurface + 4, 14⟩
    else ⟨8, Terrain.height opts.seed 8 8 + 6, 8⟩
  let camera : Camera := { base := start, pitch := -0.35, yaw := 0.15 }
  loop { world, camera } opts
  closeWindow
  return 0

end LeanMc.Shell
