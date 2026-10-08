import Basalt.Combinators
import LeanMc.Core.Start
import LeanMc.Core.Render

/-!
# Generators

Random inputs for the property tests, written against basalt's `Gen` so the
same definitions can be run, analysed or reasoned about.

They aim for the awkward cases on purpose: frames far shorter and far longer
than a tick, speeds at and beyond the limit, looks that reach past the player's
reach, mesh commands that misuse slots. Wide inputs are fine because every
generator here has a shrinker in `PropTest.Shrink`.
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

def genCommand : G Command := do
  let dig ← chance 30
  let placing ← chance 30
  let block ← genBlock
  return {
    move := ← genInput
    look := ← genLook
    dig
    place := if placing then some block else none }

/--
How long a frame took, in units of 1/60000 s. A tick is 1000. Most of the
weight is on frames that run no tick at all, or straddle a tick boundary.
-/
def genElapsed : G Nat :=
  frequency! [
    (2, fun _ => pure 0),
    (5, fun _ => chooseNat 1 450),
    (3, fun _ => chooseNat 900 1100),
    (1, fun _ => pure 1000),
    (2, fun _ => chooseNat 1001 6000),
    (1, fun _ => chooseNat 14000 200000)
  ] (by simp)

def genFrame : G Frame := do
  let placing ← chance 20
  let block ← genBlock
  return {
    move := ← genInput
    look := ← genLook
    dig := ← chance 20
    place := if placing then some block else none
    fly := ← chance 8
    elapsed := ← genElapsed }

/-- A ray near the flat world's surface and pillars: where it starts and how far it goes. -/
def genRay : G (Vec3 × Vec3) := do
  let origin : Vec3 :=
    ⟨← chooseInt 0 1310720, ← chooseInt 557056 917504, ← chooseInt 0 1310720⟩
  return (origin, ← genLook)

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

def genRenderOp : G RenderOp :=
  frequency! [
    (5, fun _ => RenderOp.mesh <$> genChunk),
    (5, fun _ => do
      -- Often on a chunk boundary, where an edit touches two or three chunks.
      let edge ← chance 40
      let coord : G Int := if edge then elements [-17, -16, -1, 0, 15, 16, 31] else chooseInt (-20) 34
      return .edit ⟨← coord, ← chooseInt 1 14, ← coord⟩ (← genBlock)),
    (1, fun _ => RenderOp.dropFar <$> genChunk),
    (2, fun _ => do
      return .draw ⟨← chooseInt (-2000000) 2000000, ← chooseInt 0 1000000,
        ← chooseInt (-2000000) 2000000⟩)
  ] (by simp)

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

end PropTest
