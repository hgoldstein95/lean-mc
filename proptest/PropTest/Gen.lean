import Basalt.Combinators
import LeanMc.Core.Start
import LeanMc.Core.Render
import LeanMc.Core.Save

/-!
# Generators

Random inputs for the property tests, written against basalt's `Gen` so the
same definitions can be run, analysed or reasoned about.

They aim for the awkward cases on purpose: frames far shorter and far longer
than a tick, speeds at and beyond the limit, looks that reach past the player's
reach, mesh commands that misuse slots. Wide inputs are fine because every
generator here has a shrinker in `PropTest.Shrink`.

Every generator a property runs is a named definition here, with no generator
bound locally inside another, so that each has a law of its own: `PropTest.Spec`
says exactly which values each can produce, and `PropTestProofs` proves it.
-/

open LeanMc

namespace PropTest

variable {G : Type → Type} [Gen G]

/-- `true` about `percent` times in a hundred. -/
def chance (percent : Nat) : G Bool := do
  return (← chooseNat 0 99) < percent

/-- A speed along one axis, in units per tick: rest, the game's own speeds, the limit, and beyond. -/
def genSpeed : G Int :=
  frequency! [
    (3, fun _ => pure 0),
    (3, fun _ => elements
      [Player.walkSpeed, -Player.walkSpeed, Player.sprintSpeed, -Player.sprintSpeed]),
    (2, fun _ => elements [65536, -65536, Player.fastFlySpeed, -Player.fastFlySpeed, 1, -1]),
    (2, fun _ => chooseInt (-70000) 70000),
    (1, fun _ => chooseInt (-2000000) 2000000)
  ] (by simp)

def genInput : G Input := do
  return {
    wishX := ← genSpeed
    wishZ := ← genSpeed
    jump := ← chance 25
    descend := ← chance 10
    toggleFly := ← chance 3 }

/-- A look vector: anywhere within reach, mostly downwards, along an axis, nowhere, or far too long. -/
def genLook : G Vec3 :=
  frequency! [
    (4, fun _ => do
      return ⟨← chooseInt (-327680) 327680, ← chooseInt (-327680) 327680,
        ← chooseInt (-327680) 327680⟩),
    (4, fun _ => do
      return ⟨← chooseInt (-150000) 150000, ← chooseInt (-327680) (-60000),
        ← chooseInt (-150000) 150000⟩),
    (1, fun _ => elements
      [(⟨0, -327680, 0⟩ : Vec3), ⟨327680, 0, 0⟩, ⟨0, 0, -327680⟩, ⟨0, 327680, 0⟩, ⟨0, 0, 0⟩,
       ⟨65536, -65536, 0⟩, ⟨-1, -1, -1⟩]),
    (1, fun _ => do
      return ⟨← chooseInt (-9000000) 9000000, ← chooseInt (-9000000) 9000000,
        ← chooseInt (-9000000) 9000000⟩)
  ] (by simp)

/-- A block to place: usually an ordinary one, sometimes bedrock or air. -/
def genBlock : G Block :=
  frequency! [
    (9, fun _ => elements
      [Block.stone, .dirt, .grass, .sand, .log, .leaves, .planks, .cobble]),
    (1, fun _ => elements [Block.bedrock, .air])
  ] (by simp)

/-- A slot key press: usually none, otherwise any of the nine slots. -/
def genSelect : G (Option (Fin 9)) := do
  let pressed ← chance 15
  let i ← chooseNat 0 8
  return if pressed then some ⟨i % 9, Nat.mod_lt _ (by decide)⟩ else none

/-- What a command asks to do to the world: often nothing, otherwise dig or place. -/
def genAction : G (Option Action) :=
  frequency! [
    (4, fun _ => pure none),
    (3, fun _ => pure (some Action.dig)),
    (3, fun _ => pure (some Action.place))
  ] (by simp)

def genCommand : G Command := do
  return {
    move := ← genInput
    look := ← genLook
    action := ← genAction
    select := ← genSelect }

/-- A run of at most `n` commands. -/
def genCommands (n : Nat) : G (List Command) :=
  listOfMaxLength n genCommand

/-- A world seed and a run of commands to play in the world generated from it. -/
def genSeededCommands : G (UInt64 × List Command) := do
  return (← elements [(2026 : UInt64), 1, 7, 99], ← genCommands 60)

/--
How long a frame took, in units of 1/60000 s. A tick is 1000. Most of the
weight is on frames that run no tick at all, or straddle a tick boundary; the
rest reach every number of ticks up to the per-frame limit and beyond it.
-/
def genElapsed : G Nat :=
  frequency! [
    (2, fun _ => pure 0),
    (5, fun _ => chooseNat 1 450),
    (3, fun _ => chooseNat 900 1100),
    (1, fun _ => pure 1000),
    (2, fun _ => chooseNat 1001 16999),
    (1, fun _ => chooseNat 14000 200000)
  ] (by simp)

def genFrame : G Frame := do
  return {
    move := ← genInput
    look := ← genLook
    dig := ← chance 20
    place := ← chance 20
    select := ← genSelect
    fly := ← chance 8
    elapsed := ← genElapsed }

/-- A run of at most 120 frames. -/
def genFrames : G (List Frame) :=
  listOfMaxLength 120 genFrame

/--
A ray near the flat world's surface and pillars: where it starts and how far it
goes. It starts on either side of the origin, so cells with negative
coordinates are walked from as well as into.
-/
def genRay : G (Vec3 × Vec3) := do
  let origin : Vec3 :=
    ⟨← chooseInt (-1310720) 1310720, ← chooseInt 557056 917504, ← chooseInt (-1310720) 1310720⟩
  return (origin, ← genLook)

/-! ## Saved games -/

/-- An integer of any size and sign, including ones too big for 64 bits. -/
def genWideInt : G Int :=
  frequency! [
    (4, fun _ => chooseInt (-70) 70),
    (3, fun _ => chooseInt (-3000000) 3000000),
    (1, fun _ => elements
      [(1000000000000000000000 : Int), -1000000000000000000000, 9223372036854775808,
       -9223372036854775809, 0, -1])
  ] (by simp)

def genAnyBlock : G Block :=
  elements [Block.air, .bedrock, .stone, .dirt, .grass, .sand, .log, .leaves, .planks, .cobble]

def genSlot9 : G (Fin 9) := do
  return ⟨(← chooseNat 0 8) % 9, Nat.mod_lt _ (by decide)⟩

/-- One slot of an inventory: empty half the time, otherwise a stack of any block and any size. -/
def genStackSlot : G (Option Stack) := do
  if ← chance 50 then
    let extra ← chooseNat 0 63
    let block ← genAnyBlock
    return some ⟨block, ⟨extra % 64, Nat.mod_lt _ (by decide)⟩⟩
  else
    return none

def genInventory : G Inventory := do
  return ⟨#v[← genStackSlot, ← genStackSlot, ← genStackSlot, ← genStackSlot, ← genStackSlot,
    ← genStackSlot, ← genStackSlot, ← genStackSlot, ← genStackSlot]⟩

/-- A position or velocity with each component an integer of any size. -/
def genWideVec : G Vec3 := do
  return ⟨← genWideInt, ← genWideInt, ← genWideInt⟩

/-- A world seed: usually small, sometimes at the edges of 32 and 64 bits. -/
def genSeed : G UInt64 := do
  let seed ← frequency! [
    (3, fun _ => chooseNat 0 100),
    (1, fun _ => elements [18446744073709551615, 9223372036854775808, 4294967296])
  ] (by simp)
  return seed.toUInt64

/-- One saved block change, anywhere at all. -/
def genEdit : G (BlockPos × Block) := do
  return ((⟨← genWideInt, ← genWideInt, ← genWideInt⟩ : BlockPos), ← genAnyBlock)

/-- A saved player: anywhere, at any speed, with any claim about the ground. -/
def genPlayer : G Player := do
  return { pos := ← genWideVec, vel := ← genWideVec, onGround := ← chance 50, flying := ← chance 50 }

/-- Any saved game at all, sound or not: the encoding has to cope with every one. -/
def genSaveData : G SaveData := do
  let seed ← genSeed
  let edits ← listOfMaxLength 12 genEdit
  return {
    seed
    player := ← genPlayer
    inventory := ← genInventory
    selected := ← genSlot9
    edits }

/-- A valid save's integers with one of them replaced by an integer of any size. -/
def genMutatedSave : G (List Int) := do
  let d ← genSaveData
  let i ← chooseNat 0 200
  return d.encode.set (i % d.encode.length) (← genWideInt)

/-! ## Renderer operations -/

/-- One thing the game asks of the render planner. -/
inductive RenderOp where
  | mesh (c : ChunkPos)
  | edit (p : BlockPos) (b : Block)
  | dropFar (centre : ChunkPos)
  | draw (eye : Vec3)
  deriving Repr

/-- A chunk near the flat world's surface. -/
def genChunk : G ChunkPos := do
  return ⟨← chooseInt (-1) 1, ← chooseInt (-1) 1, ← chooseInt (-1) 1⟩

/--
Where the view is centred when far chunks are dropped: often far enough from
the chunks `genChunk` meshes that some are dropped, their slots emptied and
later reused.
-/
def genCentre : G ChunkPos := do
  return ⟨← chooseInt (-4) 4, ← chooseInt (-4) 4, ← chooseInt (-4) 4⟩

/--
The height of an edit: usually in the ground or just above it, sometimes on or
across the boundary between one chunk and the chunk above or below, where the
edit also touches that chunk's mesh.
-/
def genEditY : G Int :=
  frequency! [
    (6, fun _ => chooseInt 1 14),
    (3, fun _ => elements [15, 16, 17, 31, 32]),
    (1, fun _ => elements [-1, 0])
  ] (by simp)

/-- A horizontal coordinate of an edit: on a chunk boundary if `edge`, else anywhere nearby. -/
def genEditCoord (edge : Bool) : G Int :=
  if edge then elements [-17, -16, -1, 0, 15, 16, 31] else chooseInt (-20) 34

/-- Where an edit lands: often on a chunk boundary, where it touches two or three chunks. -/
def genEditPos : G BlockPos := do
  let edge ← chance 40
  return ⟨← genEditCoord edge, ← genEditY, ← genEditCoord edge⟩

def genRenderOp : G RenderOp :=
  frequency! [
    (5, fun _ => RenderOp.mesh <$> genChunk),
    (5, fun _ => do return .edit (← genEditPos) (← genBlock)),
    (2, fun _ => RenderOp.dropFar <$> genCentre),
    (2, fun _ => do
      return .draw ⟨← chooseInt (-2000000) 2000000, ← chooseInt 0 1000000,
        ← chooseInt (-2000000) 2000000⟩)
  ] (by simp)

/-- A run of at most 30 renderer operations. -/
def genRenderOps : G (List RenderOp) :=
  listOfMaxLength 30 genRenderOp

/-! ## Commands to the shim -/

/-- A byte of a packed vertex: usually a small value like the real ones, sometimes anything. -/
def genByte : G UInt8 := do
  let wild ← chance 15
  return (← if wild then chooseNat 0 255 else chooseNat 0 17).toUInt8

def genBytes (n : Nat) : G ByteArray := do
  return ByteArray.mk (← vectorOf n genByte).toArray

/-- A mesh to upload: usually whole triangles, sometimes empty or cut short. -/
def genMesh : G ByteArray :=
  frequency! [
    (8, fun _ => do genBytes (24 * (← chooseNat 1 6))),
    (1, fun _ => pure ByteArray.empty),
    (1, fun _ => do genBytes (← elements [1, 8, 23, 25, 47, 50]))
  ] (by simp)

/-- A slot: usually one of a few, so commands collide; sometimes slot zero or out of range. -/
def genSlot : G Nat :=
  frequency! [
    (10, fun _ => chooseNat 1 5),
    (1, fun _ => pure 0),
    (1, fun _ => elements [16383, 16384, 16385, 70000, 4294967299])
  ] (by simp)

def genGpuCmd : G GpuCmd :=
  frequency! [
    (4, fun _ => do return .upload (← genSlot) (← genMesh)),
    (2, fun _ => GpuCmd.unload <$> genSlot),
    (4, fun _ => do
      return .draw (← genSlot)
        ⟨← chooseInt (-4000000) 4000000, ← chooseInt (-4000000) 4000000,
          ← chooseInt (-4000000) 4000000⟩),
    (1, fun _ => pure .beginScene)
  ] (by simp)

/-- A run of at most 40 commands to the shim. -/
def genGpuCmds : G (List GpuCmd) :=
  listOfMaxLength 40 genGpuCmd

/-- Bytes for the shim to read as vertices: any number of them up to 200, whole vertices or not. -/
def genDecodeBytes : G ByteArray := do
  genBytes (← chooseNat 0 200)

end PropTest
