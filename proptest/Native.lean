import PropTest.Shrink
import Basalt.IO
import LeanMc.Shell.Game

/-!
# The shim against its model

`LeanMc.Gpu` says what the native shim's mesh table should do, and the render
planner is proved correct against that description. These tests check the
description against the real thing: random command sequences are sent to the
shim through the game's own interpreter, and its state is read back and
compared with the model's.

The shim logs only the first `sceneLogSize` draws of a scene, but counts them
all. So a scene is compared in two parts: the count, and what the log holds.

This needs a window, for the graphics context. Run with `lake exe native`.
-/

open LeanMc PropTest LeanMc.FFI

/-- The twelve numbers the shim should report for a vertex: position, uv, normal, colour. -/
def expectedVertex (v : GpuVertex) : List Float :=
  let normal : List Float :=
    match v.normal with
    | 0 => [1, 0, 0] | 1 => [-1, 0, 0] | 2 => [0, 1, 0] | 3 => [0, -1, 0] | 4 => [0, 0, 1]
    | _ => [0, 0, -1]
  [v.x.toFloat, v.y.toFloat, v.z.toFloat, v.u.toFloat / 16, v.v.toFloat / 16] ++ normal
    ++ [v.shade.toFloat, v.shade.toFloat, v.shade.toFloat, 255]

def expectedMesh (vertices : ByteArray) : List Float :=
  (Gpu.decode vertices).flatMap expectedVertex

def sameFloats (a b : List Float) : Bool :=
  a.length == b.length && (a.zip b).all fun (x, y) => x == y

def showCmd : GpuCmd → String
  | .upload slot v => s!"upload {slot} ({v.size} bytes: {v.data.toList.take 24}…)"
  | .unload slot => s!"unload {slot}"
  | .beginScene => "beginScene"
  | .draw slot offset => s!"draw {slot} at {offset.x} {offset.y} {offset.z}"

def showCmds (cmds : List GpuCmd) : String :=
  s!"{cmds.length} commands: {cmds.map showCmd}"

/-- The slot a command names, if it names one. -/
def cmdSlot : GpuCmd → Option Nat
  | .upload slot _ | .unload slot | .draw slot _ => some slot
  | .beginScene => none

/--
Slots to read back after a run: every slot a command named, the ones the
generator favours, and the edges of the table.
-/
def watched (cmds : List GpuCmd) : List Nat :=
  (cmds.filterMap cmdSlot ++ [0, 1, 2, 3, 4, 5, 6, 16383, 16384, 16385, 70000]).eraseDups

/-- Does the shim read these bytes the way the model says? -/
def decodeFault (vertices : ByteArray) : IO (Option String) := do
  let got := (← debugDecode vertices).toList
  let want := expectedMesh vertices
  if sameFloats got want then return none
  return some s!"shim read {got.length / 12} vertices as {got}, model says {want}"

/--
Send commands to the shim and to a model, then compare everything that can be
read back: the fault flag, how many slots hold a mesh, each watched slot, how
many draws the scene has, and the draws the shim's log holds. `logged` is how
many draws the model says the log holds.

Slots are read back the way the shell names them, so that a slot too big for
32 bits is looked for where the shell sends it.
-/
def storeFault (exec : Gpu → GpuCmd → Gpu) (cmds : List GpuCmd) (logged : Nat := sceneLogSize) :
    IO (Option String) := do
  debugReset
  cmds.forM Shell.Game.send
  let model := cmds.foldl exec {}
  if (← debugFault) != model.fault then
    return some s!"fault flag: shim {← debugFault}, model {model.fault}"
  let live := (← debugLiveCount).toNat
  if live != model.meshes.size then
    return some s!"{live} slots of the shim hold a mesh, {model.meshes.size} of the model"
  for slot in watched cmds do
    let want := model.meshes[slot]?
    let arg := Shell.Game.slotArg slot
    if (← debugMeshLive arg) != want.isSome then
      return some s!"slot {slot}: shim live {← debugMeshLive arg}, model {want.isSome}"
    let got := (← debugMesh arg).toList
    unless sameFloats got ((want.map expectedMesh).getD []) do
      return some s!"slot {slot} holds different vertices from the model"
  let total := (← debugSceneTotal).toNat
  if total != model.scene.length then
    return some s!"scene: shim made {total} draws, model {model.scene.length}"
  let scene := (← debugScene).toList
  let want := (model.scene.take logged).flatMap fun (slot, o) =>
    [slot.toFloat, Float.ofInt o.x / 65536.0, Float.ofInt o.y / 65536.0, Float.ofInt o.z / 65536.0]
  unless sameFloats scene want do
    -- A long scene is far too much to print: say where the two part ways.
    let differ := ((scene.zip want).zipIdx.find? fun ((x, y), _) => x != y).map (·.2 / 4)
    return some s!"scene: shim logged {scene.length / 4} draws, model {want.length / 4}; \
      first difference at draw {differ}"
  return none

/-- One triangle with every byte zero: nothing to see, so cheap to draw thousands of times. -/
def emptyTriangle : ByteArray := ByteArray.mk (Array.replicate 24 0)

/--
The commands of a long scene: put a mesh in slot 1, draw it `draws` times, each
at its own offset so that the order of the draws shows, then send `tail`.
-/
def longScene (scene : Nat × List GpuCmd) : List GpuCmd :=
  .upload 1 emptyTriangle
    :: (List.range scene.1).map (fun (i : Nat) => GpuCmd.draw 1 ⟨i, 0, 0⟩) ++ scene.2

def showLongScene (scene : Nat × List GpuCmd) : String :=
  s!"upload 1, {scene.1} draws of it, then {showCmds scene.2}"

/-- A wrong model, which forgets to empty slots: the tests must notice. -/
def forgetfulExec (g : Gpu) : GpuCmd → Gpu
  | .unload _ => g
  | cmd => g.exec cmd

/-- A wrong model, which puts an upload to slot 2 in slot 9 as well: the tests must notice. -/
def strayExec (g : Gpu) : GpuCmd → Gpu
  | .upload 2 v =>
    let g := g.exec (.upload 2 v)
    { g with meshes := g.meshes.insert 9 v }
  | cmd => g.exec cmd

/-! ## The picture

Everything above reads back what the shim was told. These few checks read
back what it drew: single faces, looked at from in front and from behind, with
an atlas whose every texel says which tile it is in and which quarter of it.
They are the only tests of how the shim winds, culls, shades and textures.
-/

/--
A texel of the test atlas, which is two texels to a tile each way. Red says
which tile it is in, green whether it is in the left or right half of the tile,
and blue whether it is in the top or bottom half.
-/
def probeTexel (tile qx qy : Nat) : Nat × Nat × Nat :=
  ((60 + 12 * tile) % 256, if qx = 0 then 80 else 200, if qy = 0 then 80 else 200)

def probeAtlas : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (32 * 32 * 4)
  for y in [0:32] do
    for x in [0:32] do
      let (r, g, b) := probeTexel (y / 2 * 16 + x / 2) (x % 2) (y % 2)
      out := out.push r.toUInt8 |>.push g.toUInt8 |>.push b.toUInt8 |>.push 255
  return out

/-- What is seen where nothing is drawn. No face of the test atlas comes near it. -/
def probeSky : Nat × Nat × Nat := (255, 0, 255)

/-- The colour a face shows where its texture has the given texel: the texel, dimmed by the face's shade. -/
def shaded (d : Dir) (texel : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let dim (v : Nat) : Nat := v * d.shade.toNat / 255
  (dim texel.1, dim texel.2.1, dim texel.2.2)

/-- Whether two colours are the same to within rounding. -/
def nearColour (a b : Nat × Nat × Nat) : Bool :=
  let near (x y : Nat) : Bool := x ≤ y + 2 && y ≤ x + 2
  near a.1 b.1 && near a.2.1 b.2.1 && near a.2.2 b.2.2

def showColour (c : Nat × Nat × Nat) : String :=
  s!"({c.1}, {c.2.1}, {c.2.2})"

/-- The same triangles with their corners in the opposite order, so facing the other way. -/
def rewound (vertices : ByteArray) : ByteArray :=
  ((List.range (vertices.size / 8)).reverse.foldl (init := ByteArray.empty) fun out i =>
    out ++ vertices.extract (i * 8) (i * 8 + 8))

/--
Draw one face of a block and read back four points around the middle of the
screen, one in each quarter of the face. The eye is two blocks from the middle
of the face, on the side its normal points to if `front` and on the other side
if not, and looks straight at it; for a top or bottom face it stands a block
to one side as well, since the shim's camera cannot look straight up or down.
The result is each point's place on the screen, left or right and top or
bottom, with the colour found there.
-/
def probeFace (b : Block) (d : Dir) (front : Bool) (rewind : Bool := false) :
    IO (List ((Nat × Nat) × (Nat × Nat × Nat))) := do
  let pos : LocalPos := ⟨8, 8, 8⟩
  let mesh := packFaces [⟨pos, d, b⟩]
  let n := (⟨0, 0, 0⟩ : BlockPos).step d
  -- Everything here is in half blocks, so that the middle of a face is a whole number.
  let side : Int := if front then -4 else 4
  let target : Vec3 := ⟨side * n.x, side * n.y, side * n.z - (if n.y = 0 then 0 else 2)⟩
  let middle : Vec3 := ⟨17 + n.x, 17 + n.y, 17 + n.z⟩
  let offset : Vec3 :=
    ⟨(target.x - middle.x) * 32768, (target.y - middle.y) * 32768, (target.z - middle.z) * 32768⟩
  debugReset
  beginFrame 0xff00ffff
  begin3D 0 0 0 (Float.ofInt target.x) (Float.ofInt target.y) (Float.ofInt target.z) 70.0
  [GpuCmd.upload 1 (if rewind then rewound mesh else mesh), .beginScene, .draw 1 offset].forM
    Shell.Game.send
  end3D
  let mut seen := []
  for (sx, sy) in [(0, 0), (1, 0), (0, 1), (1, 1)] do
    let place (s : Nat) : Float := if s = 0 then 0.46 else 0.54
    let rgba := (← debugPixel (place sx) (place sy)).toNat
    seen := seen ++ [((sx, sy), (rgba >>> 24, (rgba >>> 16) % 256, (rgba >>> 8) % 256))]
  endFrame
  return seen

/--
The first face that does not look as the mesh theorems and the model say it
should, if any. From in front, each quarter of a side face shows the same
quarter of its block's tile, dimmed by the face's shade: left for left and top
for top, as `Dir.uv_upright` has it. A top or bottom face shows its tile and
shade; which way round is not checked. From behind, no face is seen at all.
-/
def pictureFault (rewind : Bool := false) : IO (Option String) := do
  let blocks : List Block := [.bedrock, .stone, .dirt, .grass, .sand, .log, .leaves, .planks, .cobble]
  for b in blocks do
    for d in Dir.all do
      let tile := b.tile d
      let quarters := [(0, 0), (1, 0), (0, 1), (1, 1)].map fun (qx, qy) =>
        shaded d (probeTexel tile qx qy)
      for ((sx, sy), got) in ← probeFace b d true rewind do
        let ok :=
          if d = .yp ∨ d = .yn then quarters.any (nearColour got)
          else nearColour got (shaded d (probeTexel tile sx sy))
        unless ok do
          return some s!"the {repr d} face of {repr b}, from in front, shows {showColour got} at \
            {if sx = 0 then "left" else "right"} {if sy = 0 then "top" else "bottom"}; \
            its tile there is {showColour (shaded d (probeTexel tile sx sy))}, and the sky is \
            {showColour probeSky}"
      for (_, got) in ← probeFace b d false rewind do
        unless nearColour got probeSky do
          return some s!"the {repr d} face of {repr b} shows {showColour got} from behind"
  return none

/-- Run a check that has no input to generate. `wantFault` is whether it should find one. -/
def checks (name : String) (wantFault : Bool) (test : IO (Option String)) : IO Bool := do
  match ← test, wantFault with
  | none, false =>
    IO.println s!"ok    {name}"
    return true
  | some found, true =>
    IO.println s!"ok    {name} (found: {found})"
    return true
  | some found, false =>
    IO.println s!"FAIL  {name}: {found}"
    return false
  | none, true =>
    IO.println s!"FAIL  {name}: nothing was found wrong"
    return false

def parseArgs (runs seed : Nat) : List String → Nat × Nat
  | "--runs" :: n :: rest => parseArgs (n.toNat?.getD runs) seed rest
  | "--seed" :: n :: rest => parseArgs runs (n.toNat?.getD seed) rest
  | _ :: rest => parseArgs runs seed rest
  | [] => (runs, seed)

@[export lmc_native_main]
def nativeMain (args : List String) : IO UInt32 := do
  let (runs, seed) := parseArgs 300 (← IO.monoNanosNow) args
  ioGen.set (SplitMix.ofSeed seed.toUInt64)
  IO.println s!"shim against model: {runs} runs each, seed {seed}"
  initWindow 320 240 "lean-mc shim tests"
  let mut ok := true

  ok := (← holds "the shim reads vertices the way the model says" (runs * 3)
    genDecodeBytes shrinkMesh
    (fun v => s!"{v.size} bytes: {v.data.toList}") decodeFault) && ok

  ok := (← holds "the shim's mesh table and scene match the model after any commands" runs
    genGpuCmds (shrinkList shrinkGpuCmd) showCmds (storeFault Gpu.exec)) && ok

  ok := (← refutes "self-check: a model that forgets to unload is caught" runs
    genGpuCmds (shrinkList shrinkGpuCmd) List.length 2 showCmds
    (storeFault forgetfulExec)) && ok

  -- Slot 9 is never named by a command, so only the count of live slots can show this.
  ok := (← refutes "self-check: a model that fills a slot no command names is caught" runs
    genGpuCmds (shrinkList shrinkGpuCmd) List.length 1 showCmds
    (storeFault strayExec)) && ok

  -- These send thousands of commands a run, so they get fewer runs.
  ok := (← holds "a scene longer than the shim's log is counted and logged as the model says"
    (runs / 10 + 1) genLongScene (shrinkPair shrinkNat (shrinkList shrinkGpuCmd)) showLongScene
    (fun scene => storeFault Gpu.exec (longScene scene))) && ok

  ok := (← refutes "self-check: a scene outgrows the shim's log" (runs / 10 + 1)
    genLongScene (shrinkPair shrinkNat (shrinkList shrinkGpuCmd)) (·.1) (sceneLogSize + 1)
    showLongScene
    (fun scene => storeFault Gpu.exec (longScene scene) (logged := sceneLogSize + 1))) && ok

  setAtlas 32 32 probeAtlas
  ok := (← checks "a face is drawn with its own tile and shade, the right way up, and only from in front"
    false pictureFault) && ok

  ok := (← checks "self-check: a face wound the other way is not seen from in front" true
    (pictureFault (rewind := true))) && ok

  debugReset
  closeWindow
  return if ok then 0 else 1
