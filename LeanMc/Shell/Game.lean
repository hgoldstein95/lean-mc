import LeanMc.FFI
import LeanMc.Core.World
import LeanMc.Core.Mesh
import LeanMc.Core.Generated
import LeanMc.Core.Start
import LeanMc.Core.View
import LeanMc.Core.Render
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

/-- How far chunks are kept loaded around the player. -/
def view : ViewRange := ⟨6, 4⟩

def blockName : Block → String
  | .air => "air" | .bedrock => "bedrock" | .stone => "stone" | .dirt => "dirt"
  | .grass => "grass" | .sand => "sand" | .log => "log" | .leaves => "leaves"
  | .planks => "planks" | .cobble => "cobble"

structure Game where
  /-- The simulated game and the bookkeeping that paces it; all of it lives in the core. -/
  session : Session
  /-- The render planner's memory: cached chunks and which mesh slot each chunk holds. -/
  renderer : Renderer := {}
  /-- Where the player was one tick ago, so that drawing can blend between ticks. -/
  prevPos : Vec3
  yaw : Float := 0.0
  pitch : Float := 0.0
  captured : Bool := false
  /-- Number of blocks dug or placed so far. -/
  edits : Nat := 0
  /-- Number of ticks simulated so far. -/
  ticks : Nat := 0
  frame : Nat := 0

/--
Offsets of every chunk in view of a centre chunk, nearest first. Which offsets
there are comes from the core (`ViewRange.contains_iff_offset`); the shell only
chooses the order.
-/
def chunkOffsets : Array (Int × Int × Int) :=
  let dist := fun (o : Int × Int × Int) => o.1 * o.1 + o.2.1 * o.2.1 + o.2.2 * o.2.2
  view.offsets.toArray.qsort fun a b => dist a < dist b

namespace Game

def state (g : Game) : State := g.session.state
def world (g : Game) : World := g.session.state.world
def player (g : Game) : Player := g.session.state.player

/-- Unit vector the player looks along. Yaw `0` faces `-z`. -/
def lookDir (g : Game) : Float × Float × Float :=
  (g.yaw.sin * g.pitch.cos, g.pitch.sin, -(g.yaw.cos * g.pitch.cos))

/--
The eye position to draw from, in fixed-point units: the player's eyes, blended
between the last two ticks by how far into the current tick the frame falls.
-/
def eye (g : Game) : Vec3 :=
  let blend : Int := (min g.session.debt unitsPerTick * 1024 / unitsPerTick : Nat)
  let mix (a b : Int) : Int := a + (b - a) * blend / 1024
  ⟨mix g.prevPos.x g.player.pos.x,
   mix g.prevPos.y g.player.pos.y + Player.eyeHeight,
   mix g.prevPos.z g.player.pos.z⟩

/-- The view direction as a vector to the limit of the player's reach, in units. -/
def lookVector (g : Game) : Vec3 :=
  let (dx, dy, dz) := g.lookDir
  let scale := State.reach.toFloat
  ⟨(dx * scale).toInt64.toInt, (dy * scale).toInt64.toInt, (dz * scale).toInt64.toInt⟩

/--
A slot number as the shim takes it. Numbers too big for 32 bits are pinned to
the largest, which is out of the shim's range, so that they are refused as the
model says they should be and do not wrap round to a valid slot.
-/
def slotArg (slot : Nat) : UInt32 :=
  (min slot 0xFFFFFFFF).toUInt32

/-- Carry out one instruction from the planner. This is the whole of the shell's rendering logic. -/
def send : GpuCmd → IO Unit
  | .upload slot vertices => meshUpload (slotArg slot) vertices
  | .unload slot => meshUnload (slotArg slot)
  | .beginScene => sceneBegin
  | .draw slot offset =>
    meshDraw (slotArg slot) (Float.ofInt offset.x / 65536.0) (Float.ofInt offset.y / 65536.0)
      (Float.ofInt offset.z / 65536.0)

/-- Take a planning step: keep the planner's new memory and carry out its instructions. -/
def plan (g : Game) (step : Renderer × List GpuCmd) : IO Game := do
  step.2.forM send
  return { g with renderer := step.1 }

/--
Change one block directly, outside the simulation, to set up a test scene. The
core refuses a change that would leave the state unsound; such a change is
skipped.
-/
def setBlock (g : Game) (p : BlockPos) (b : Block) : IO Game := do
  match g.session.edit? p b with
  | some session =>
    let g := { g with session }
    g.plan (g.renderer.applyEdit g.world p b)
  | none => return g

/-- Mesh missing chunks around the player, nearest first, for up to `budgetMs`. -/
def stream (g : Game) (budgetMs : Nat) : IO Game := do
  let centre := g.eye.blockPos.chunkPos
  let start ← IO.monoMsNow
  let mut g := g
  for o in chunkOffsets do
    let c := ViewRange.offsetChunk centre o
    unless g.renderer.slots.contains c do
      g ← g.plan (g.renderer.remesh g.world c)
      if (← IO.monoMsNow) - start ≥ budgetMs then
        break
  return g

/-- Drop meshes and cached chunks that are well out of view. -/
def unloadFar (g : Game) : IO Game :=
  g.plan (g.renderer.dropFar view g.eye.blockPos.chunkPos)

/--
Advance the simulation by one frame. The core decides how many ticks run, what
each is told and what changes, and the planner decides what to rebuild.
-/
def advance (g : Game) (frame : Frame) : IO Game := do
  let ran := g.session.ticksDue frame
  let before := g.world
  let (session, log) := g.session.frameLog frame
  let mut g := { g with
    session
    prevPos := log.before.getD g.prevPos
    ticks := g.ticks + ran
    edits := g.edits + log.edits.size }
  -- Replay the block changes one at a time so the planner sees each world in turn.
  let mut world := before
  for (p, b) in log.edits do
    world := world.set p b
    g ← g.plan (g.renderer.applyEdit world p b)
  return g

/-- Turn the mouse into a view direction and handle capturing it. -/
def look (g : Game) : IO Game := do
  let mut g := g
  if (← keyPressed Key.escape) && g.captured then
    setCursorCaptured false
    g := { g with captured := false }
  if g.captured then
    let pitch := g.pitch - (← mouseDy) * 0.003
    g := { g with yaw := g.yaw + (← mouseDx) * 0.003, pitch := max (-1.55) (min 1.55 pitch) }
  return g

/-- Read the keyboard as the player's movement for a tick. -/
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
  }

/--
Read this frame's input. A click while the mouse is free only captures it;
once captured, left digs and right places.
-/
def readFrame (g : Game) : IO (Game × Frame) := do
  let left ← mousePressed Mouse.left
  let right ← mousePressed Mouse.right
  let seconds := min 0.25 (← frameTime)
  let frame : Frame := {
    move := ← g.readInput
    look := g.lookVector
    dig := g.captured && left
    place := g.captured && right
    select := ← do
      let mut chosen : Option (Fin 9) := none
      for i in List.finRange 9 do
        if ← keyPressed (Key.one + i.val.toUInt32) then
          chosen := some i
      pure chosen
    fly := ← keyPressed Key.f
    elapsed := (seconds * (unitsPerTick * ticksPerSecond).toFloat).toUInt64.toNat
  }
  if left && !g.captured then
    setCursorCaptured true
    return ({ g with captured := true }, frame)
  return (g, frame)

def draw (g : Game) : IO Unit := do
  let eye := g.eye
  beginFrame 0x87b5ffff
  let (dx, dy, dz) := g.lookDir
  begin3D 0 0 0 dx dy dz 70.0
  -- The planner's offsets are measured from the eye, so the camera sits at the origin.
  let draws := g.renderer.drawCmds eye
  draws.forM send
  let drawn := draws.length - 1
  if let some hit := g.state.target g.lookVector then
    let b := hit.block
    let rel (block eye : Int) : Float := Float.ofInt (block * 65536 - eye) / 65536.0 - 0.003
    drawBoxWires (rel b.x eye.x) (rel b.y eye.y) (rel b.z eye.z) 1.006 1.006 1.006 0x000000ff
  end3D
  let w ← screenWidth
  let h ← screenHeight
  drawRect (w / 2 - 1) (h / 2 - 8) 2 16 0xffffffff
  drawRect (w / 2 - 8) (h / 2 - 1) 16 2 0xffffffff
  let fps := (1.0 / (← frameTime)).round.toUInt32
  let feet := g.player.pos.blockPos
  let mode := if g.player.flying then "flying" else if g.player.onGround then "on ground" else "in air"
  drawText s!"block {feet.x} {feet.y} {feet.z}   {mode}   {fps} fps" 10 10 20 0xffffffff
  drawText s!"chunks {g.renderer.slots.size} meshed, {drawn} drawn, \
      {g.renderer.cache.chunks.size} cached"
    10 34 16 0xffffffff
  -- The hotbar: nine slots along the bottom, the selected one outlined.
  let slot : UInt32 := 44
  let left := w / 2 - slot * 9 / 2
  let top := h - slot - 60
  for i in List.finRange 9 do
    let x := left + i.val.toUInt32 * slot
    let chosen := i == g.state.selected
    drawRect x top slot slot (if chosen then 0xffffffff else 0x00000080)
    drawRect (x + 2) (top + 2) (slot - 4) (slot - 4) 0x30303080
    if let some stack := g.state.inventory.stack i then
      drawTile (stack.block.tile .xp).toUInt32 (x + 6) (top + 6) (slot - 12)
      drawText s!"{stack.count}" (x + 5) (top + slot - 19) 16 0xffffffff
  if let some stack := g.state.inventory.stack g.state.selected then
    drawText (blockName stack.block) left (top - 22) 16 0xffffffff
  unless g.captured do
    drawText "click to capture the mouse   WASD: move   space: jump   ctrl: sprint   F: fly"
      10 (h - 46) 16 0xffffffff
    drawText "left click: dig   right click: place   1-9: choose slot   esc: release the mouse"
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
  /-- Check input handling with made-up frames instead of playing. -/
  inputtest : Bool := false

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
  | "--inputtest" :: rest => parse { opts with inputtest := true } rest
  | "--frames" :: n :: rest =>
    match n.toNat? with
    | some n => parse { opts with frames := some n } rest
    | none => throw "--frames expects a number"
  | arg :: _ => throw s!"unknown argument: {arg}"

def flytestFrames : Nat := 240

/--
What the scripted tests do on a given frame: where the player looks and what
they ask for.
-/
def scripted (opts : Options) (g : Game) : Game × Frame :=
  if opts.flytest.isSome then
    -- Take off, then fly fast and diagonally while climbing clear of the hills.
    (g, { move := { wishX := 65536, wishZ := -21845, jump := true }, fly := g.frame == 0
          elapsed := unitsPerTick })
  else
    -- Walk forward and hop; look down and dig a shaft; then look at the ground
    -- to one side and put three of the four blocks just dug back down.
    let f := g.frame
    let g := if f == 100 then { g with pitch := -1.1, yaw := 0.0 } else g
    let g := if f == 145 then { g with pitch := -0.45, yaw := 0.7 } else g
    let walking := 40 ≤ f && f < 90
    let dig := 110 ≤ f && f < 140 && f % 6 == 0
    let place := 150 ≤ f && f < 165 && f % 6 == 0
    (g, { move := { wishZ := if walking then -Player.walkSpeed else 0, jump := f == 60 }
          look := g.lookVector, dig, place, elapsed := unitsPerTick })

partial def loop (g : Game) (opts : Options) : IO Unit := do
  if ← windowShouldClose then return
  let isScripted := opts.selftest.isSome || opts.flytest.isSome
  let mut g ← g.look
  -- Scripted runs take exactly one tick per frame so that they are repeatable.
  if isScripted then
    let (g', frame) := scripted opts g
    g ← g'.advance frame
  else
    let (g', frame) ← g.readFrame
    g ← g'.advance frame
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
    IO.println s!"frame {g.frame}: {g.renderer.slots.size} meshed, \
      {g.renderer.cache.chunks.size} cached, shim faults: {← debugFault}, \
      feet at {p.pos.x} {p.pos.y} {p.pos.z} units, block {p.pos.blockPos.x} {p.pos.blockPos.y} \
      {p.pos.blockPos.z}, onGround {p.onGround}, flying {p.flying}, {g.edits} blocks dug or \
      placed, carrying {(List.finRange 9).filterMap fun i =>
        (g.state.inventory.stack i).map fun s => s!"{s.count} {blockName s.block}"}, \
      {g.ticks} ticks, inside something solid: {Player.blocked g.world.solid p.pos}"
  match opts.selftest, opts.flytest with
  | some path, _ => if g.frame == 230 then return ← finish path
  | _, some path => if g.frame == flytestFrames then return ← finish path
  | _, _ => if opts.frames == some g.frame then return ← finish ""
  endFrame
  loop { g with frame := g.frame + 1 } opts

/--
Check, through the shell's own frame path, that presses are not lost when
frames come faster than ticks. Frames are a 240th of a second long, so most run
no tick, and each press is delivered on a frame that runs none.

The rule itself is proved in `LeanMc.Proofs.Session`; this checks that the
shell is wired to it and mirrors the resulting edits.
-/
def inputTest (g : Game) : IO UInt32 := do
  let quarter : Nat := unitsPerTick / 4
  -- Deliver `frame` on the next frame that will not tick, then run a few more frames.
  let press (g : Game) (frame : Frame) : IO Game := do
    let mut g := g
    let mut sent := false
    for _ in [0:24] do
      let quiet := g.session.debt + quarter < unitsPerTick
      let now := quiet && !sent
      let look := g.lookVector
      g ← g.advance (if now then { frame with look, elapsed := quarter } else { look, elapsed := quarter })
      sent := sent || now
    return g
  let mut g ← g.stream 100000
  for _ in [0:60] do
    g ← g.advance { elapsed := unitsPerTick }
  let mut ok := true
  let report (name : String) (pass : Bool) : IO Bool := do
    IO.println s!"{if pass then "ok  " else "FAIL"}  {name}"
    return pass
  g := { g with pitch := -1.1, yaw := 0.0 }
  let before := g.edits
  let target := g.state.target g.lookVector
  g ← press g { dig := true }
  ok := (← report "a dig pressed between ticks still digs" (g.edits == before + 1)) && ok
  ok := (← report "the dug block is gone from the world and from the cache" <|
    match target with
    | some hit =>
      g.world.get hit.block == .air && g.renderer.cache.blockAt g.world hit.block == .air
    | none => false) && ok
  g := { g with pitch := -0.45, yaw := 0.7 }
  let before := g.edits
  g ← press g { place := true }
  ok := (← report "a place pressed between ticks still places" (g.edits == before + 1)) && ok
  g ← press g { fly := true }
  ok := (← report "a fly toggle pressed between ticks still toggles" g.player.flying) && ok
  let before := g.edits
  g ← press g {}
  ok := (← report "no press, no edit" (g.edits == before && g.player.flying)) && ok
  return if ok then 0 else 1

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
      IO.eprintln "usage: leanmc [--seed N] [--flat] [--at X Y Z] [--frames N] [--selftest PNG | --flytest PNG | --inputtest]"
      return 2
  -- A session can only be built with a proof that its state is sound: either the
  -- generated world's own start, or a position the core has checked.
  let started : Option Session :=
    if opts.flat then
      let pos := standNear Terrain.flatWorld (opts.start.getD ⟨7, 12, 14⟩)
      Session.start? Terrain.flatWorld Terrain.flatWorld_floor { pos }
    else
      match opts.start with
      | none => some (Terrain.session opts.seed)
      | some b =>
        let world := Terrain.world opts.seed
        Session.start? world (Terrain.world_floor_get opts.seed) { pos := standNear world b }
  let some session := started
    | IO.eprintln "there is nowhere to stand at that position"
      return 1
  let pos := session.state.player.pos
  initWindow 1280 720 "lean-mc"
  setAtlas Atlas.size.toUInt32 Atlas.size.toUInt32 Atlas.pixels
  let game : Game := { session, prevPos := pos, pitch := -0.35, yaw := 0.15 }
  if opts.inputtest then
    let code ← inputTest game
    closeWindow
    return code
  loop game opts
  closeWindow
  return 0

end LeanMc.Shell
