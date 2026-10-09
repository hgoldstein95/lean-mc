import PropTest.Gen

/-!
# What each generator can produce

For every generator in `PropTest.Gen`, the set of values it can produce, stated
as a predicate with no generator in it. `PropTestProofs` proves each generator
sound and complete for its predicate: it produces nothing outside the set and
can produce everything in it.

Each predicate is decidable, so the tests also check it on the values that are
actually drawn.
-/

open LeanMc

namespace PropTest.Spec

/-- `v` lies between `lo` and `hi`, inclusive. -/
def Within (lo hi v : Int) : Prop :=
  lo ≤ v ∧ v ≤ hi

instance (lo hi v : Int) : Decidable (Within lo hi v) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Every component of `v` is at most `r` in size. -/
def Cube (r : Int) (v : Vec3) : Prop :=
  Within (-r) r v.x ∧ Within (-r) r v.y ∧ Within (-r) r v.z

instance (r : Int) (v : Vec3) : Decidable (Cube r v) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Commands and frames -/

/-- A speed `genSpeed` can ask for: up to about thirty times the game's limit. -/
def Speed (v : Int) : Prop :=
  Within (-2000000) 2000000 v

instance (v : Int) : Decidable (Speed v) :=
  inferInstanceAs (Decidable (Within _ _ _))

/-- An input `genInput` can produce: any keys, with both wished speeds as `genSpeed` gives. -/
def InputOK (i : Input) : Prop :=
  Speed i.wishX ∧ Speed i.wishZ

instance (i : Input) : Decidable (InputOK i) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A look `genLook` can produce: up to about 137 blocks along each axis, far past the reach. -/
def LookOK (v : Vec3) : Prop :=
  Cube 9000000 v

instance (v : Vec3) : Decidable (LookOK v) :=
  inferInstanceAs (Decidable (Cube _ _))

/-- A command `genCommand` can produce: any action and slot choice, with such an input and look. -/
def CommandOK (c : Command) : Prop :=
  InputOK c.move ∧ LookOK c.look

instance (c : Command) : Decidable (CommandOK c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A frame time `genElapsed` can produce: under half a tick, or from 0.9 to 200 ticks. -/
def ElapsedOK (n : Nat) : Prop :=
  n ≤ 450 ∨ (900 ≤ n ∧ n ≤ 200000)

instance (n : Nat) : Decidable (ElapsedOK n) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A frame `genFrame` can produce: any presses, with such an input, look and time. -/
def FrameOK (f : Frame) : Prop :=
  InputOK f.move ∧ LookOK f.look ∧ ElapsedOK f.elapsed

instance (f : Frame) : Decidable (FrameOK f) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A ray `genRay` can produce: starting within 20 blocks of the origin, 8.5 to 14 blocks up. -/
def RayOK (r : Vec3 × Vec3) : Prop :=
  Within (-1310720) 1310720 r.1.x ∧ Within 557056 917504 r.1.y
    ∧ Within (-1310720) 1310720 r.1.z ∧ LookOK r.2

instance (r : Vec3 × Vec3) : Decidable (RayOK r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A seed and commands `genSeededCommands` can produce. -/
def SeededCommandsOK (p : UInt64 × List Command) : Prop :=
  p.1 ∈ [(2026 : UInt64), 1, 7, 99] ∧ p.2.length ≤ 60 ∧ ∀ c ∈ p.2, CommandOK c

instance (p : UInt64 × List Command) : Decidable (SeededCommandsOK p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Saved games -/

/-- An integer `genWideInt` can produce: up to three million in size, or one of four far larger. -/
def Wide (n : Int) : Prop :=
  Within (-3000000) 3000000 n
    ∨ n ∈ [(1000000000000000000000 : Int), -1000000000000000000000, 9223372036854775808,
        -9223372036854775809]

instance (n : Int) : Decidable (Wide n) :=
  inferInstanceAs (Decidable (_ ∨ _))

def WideVec (v : Vec3) : Prop :=
  Wide v.x ∧ Wide v.y ∧ Wide v.z

instance (v : Vec3) : Decidable (WideVec v) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A seed `genSeed` can produce: up to 100, or at the edge of 32 or 64 bits. -/
def SeedOK (s : UInt64) : Prop :=
  s.toNat ≤ 100 ∨ s.toNat ∈ [18446744073709551615, 9223372036854775808, 4294967296]

instance (s : UInt64) : Decidable (SeedOK s) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- An edit `genEdit` can produce: any block, at wide coordinates. -/
def EditOK (e : BlockPos × Block) : Prop :=
  Wide e.1.x ∧ Wide e.1.y ∧ Wide e.1.z

instance (e : BlockPos × Block) : Decidable (EditOK e) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A player `genPlayer` can produce: any flags, at a wide position and velocity. -/
def PlayerOK (p : Player) : Prop :=
  WideVec p.pos ∧ WideVec p.vel

instance (p : Player) : Decidable (PlayerOK p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/--
A saved game `genSaveData` can produce. Nothing here says the game is sound:
the generator is meant to produce saves that load and saves that do not.
-/
def SaveOK (d : SaveData) : Prop :=
  SeedOK d.seed ∧ PlayerOK d.player ∧ d.edits.length ≤ 12 ∧ ∀ e ∈ d.edits, EditOK e

instance (d : SaveData) : Decidable (SaveOK d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- What `genMutatedSave` can produce: such a save's integers with any one replaced by a wide one. -/
def MutatedSaveOK (ints : List Int) : Prop :=
  ∃ d, SaveOK d ∧ ∃ j, j < d.encode.length ∧ ∃ w, Wide w ∧ ints = d.encode.set j w

/-! ## Renderer operations -/

/-- A chunk `genChunk` can produce: the origin chunk or one touching it. -/
def ChunkOK (c : ChunkPos) : Prop :=
  Within (-1) 1 c.x ∧ Within (-1) 1 c.y ∧ Within (-1) 1 c.z

instance (c : ChunkPos) : Decidable (ChunkOK c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A view centre `genCentre` can produce: up to four chunks from the origin each way. -/
def CentreOK (c : ChunkPos) : Prop :=
  Within (-4) 4 c.x ∧ Within (-4) 4 c.y ∧ Within (-4) 4 c.z

instance (c : ChunkPos) : Decidable (CentreOK c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A height `genEditY` can produce: from just below the floor to just into the chunk above, or two chunks up. -/
def EditYOK (y : Int) : Prop :=
  Within (-1) 17 y ∨ y = 31 ∨ y = 32

instance (y : Int) : Decidable (EditYOK y) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A horizontal coordinate `genEditCoord edge` can produce. -/
def EditCoordOK (edge : Bool) (v : Int) : Prop :=
  if edge then v ∈ [(-17 : Int), -16, -1, 0, 15, 16, 31] else Within (-20) 34 v

instance (edge : Bool) (v : Int) : Decidable (EditCoordOK edge v) := by
  unfold EditCoordOK
  infer_instance

/-- A position `genEditPos` can produce. -/
def EditPosOK (p : BlockPos) : Prop :=
  Within (-20) 34 p.x ∧ EditYOK p.y ∧ Within (-20) 34 p.z

instance (p : BlockPos) : Decidable (EditPosOK p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A renderer operation `genRenderOp` can produce. -/
def RenderOpOK : RenderOp → Prop
  | .mesh c => ChunkOK c
  | .edit p _ => EditPosOK p
  | .dropFar c => CentreOK c
  | .draw e => Within (-2000000) 2000000 e.x ∧ Within 0 1000000 e.y ∧ Within (-2000000) 2000000 e.z

instance (op : RenderOp) : Decidable (RenderOpOK op) := by
  cases op <;> simp only [RenderOpOK] <;> infer_instance

/-! ## Commands to the shim -/

/-- A mesh size `genMesh` can produce: one to six whole triangles, none, or a ragged few bytes. -/
def MeshSizeOK (n : Nat) : Prop :=
  n ∈ [24, 48, 72, 96, 120, 144, 0, 1, 8, 23, 25, 47, 50]

instance (n : Nat) : Decidable (MeshSizeOK n) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- A slot `genSlot` can produce: zero to five, or one at or past the edge of the table. -/
def SlotOK (n : Nat) : Prop :=
  n ≤ 5 ∨ n ∈ [16383, 16384, 16385, 70000, 4294967299]

instance (n : Nat) : Decidable (SlotOK n) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A shim command `genGpuCmd` can produce. -/
def GpuCmdOK : GpuCmd → Prop
  | .upload slot vertices => SlotOK slot ∧ MeshSizeOK vertices.size
  | .unload slot => SlotOK slot
  | .beginScene => True
  | .draw slot offset => SlotOK slot ∧ Cube 4000000 offset

instance (cmd : GpuCmd) : Decidable (GpuCmdOK cmd) := by
  cases cmd <;> simp only [GpuCmdOK] <;> infer_instance

end PropTest.Spec
