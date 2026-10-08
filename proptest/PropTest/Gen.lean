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

def genCommand : G Command := do
  return {
    move := ← genInput
    look := ← genLook
    dig := ← chance 35
    place := ← chance 35
    select := ← genSelect }

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
  return {
    move := ← genInput
    look := ← genLook
    dig := ← chance 20
    place := ← chance 20
    select := ← genSelect
    fly := ← chance 8
    elapsed := ← genElapsed }

/-- A ray near the flat world's surface and pillars: where it starts and how far it goes. -/
def genRay : G (Vec3 × Vec3) := do
  let origin : Vec3 :=
    ⟨← chooseInt 0 1310720, ← chooseInt 557056 917504, ← chooseInt 0 1310720⟩
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

def genInventory : G Inventory := do
  let mut slots : Vector (Option Stack) 9 := Vector.replicate 9 none
  for i in List.finRange 9 do
    if ← chance 50 then
      let extra : Fin 64 := ⟨(← chooseNat 0 63) % 64, Nat.mod_lt _ (by decide)⟩
      slots := slots.set i (some ⟨← genAnyBlock, extra⟩)
  return ⟨slots⟩

/-- Any saved game at all, sound or not: the encoding has to cope with every one. -/
def genSaveData : G SaveData := do
  let vec : G Vec3 := do return ⟨← genWideInt, ← genWideInt, ← genWideInt⟩
  let seed ← frequency! [
    (3, fun _ => chooseNat 0 100),
    (1, fun _ => elements [18446744073709551615, 9223372036854775808, 4294967296])
  ] (by simp)
  let edits ← listOfMaxLength 12 (do
    return ((⟨← genWideInt, ← genWideInt, ← genWideInt⟩ : BlockPos), ← genAnyBlock))
  return {
    seed := seed.toUInt64
    player := { pos := ← vec, vel := ← vec, onGround := ← chance 50, flying := ← chance 50 }
    inventory := ← genInventory
    selected := ← genSlot9
    edits }

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
