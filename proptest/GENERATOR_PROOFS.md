# Plan: proving the property-test generators and shrinkers correct

A plan, not yet carried out. The Lean signatures are proposals that have not
been through the elaborator. It was drawn up from reading `PropTest/Gen.lean`,
`PropTest/Shrink.lean`, `Props.lean`, `Native.lean` and basalt's sources, and
then brought up to date with the generator fixes listed in section 1.

## 1. Findings from reading the generators

Fixed already (in `Gen.lean` / `Props.lean`), each with a `refutes` self-check
so the hole cannot quietly reopen:

- **The render property never emptied or reused a slot.** `.dropFar` centres
  came from `genChunk` (`[-1,1]³`), the same cube as the meshed chunks, so with
  view `⟨1,1⟩` nothing was ever far; and edits had `y ∈ [1,14]`, so no chunk's
  mesh ever became empty. `Renderer.free` was always `[]`, `alloc` always took
  a fresh slot and no `.unload` was ever sent, although "the planner misused
  the shim" and "two chunks share a slot" are about exactly that code. Now
  `genCentre` ranges over `[-4,4]³` and `genEditY` reaches other chunks.
  Self-checks: "the planner empties a slot", "the planner reuses an emptied
  slot".
- **No edit touched a vertical chunk boundary.** With `y ∈ [1,14]`,
  `dirtyChunks p` never contained a chunk above or below, though
  `mem_dirtyChunks` and `Synced.applyEdit` cover all six directions. `genEditY`
  now includes `15, 16, 17, 31, 32, -1, 0`. Self-check: "an edit touches the
  chunk above or below".
- **No frame ran 7 to 13 ticks.** `genElapsed` now covers `1001..16999`.
- **Ray origins were never negative.** `genRay` now starts on both sides of
  the origin in `x` and `z`.
- `Props.lean` started its flat session with `onGround := false` while standing
  on the ground, which the stricter `Session.start?` refuses; it now uses
  `Player.resting`. `genCommand`/`shrinkCommand` moved to `Command.action`.

Still open:

- **A dig refused for lack of room is effectively unreachable** in the command
  properties: it is in the support but needs about 130 well-aimed digs in at
  most 150 commands. Support-level coverage cannot see this. A second start
  state with a full inventory, plus a `refutes` "a dig can be refused for lack
  of room", would close it. (`Tests.lean` does cover the case directly.)
- **Loadable saves are rare** from `genSaveData`: roughly 0.3% of draws pass
  `restore?` now that speed, `onGround` and bedrock are checked. No current
  property needs a loadable save. If one is added, generate saves that are
  sound by construction: play frames from `Terrain.session seed` and take
  `.snapshot`; `Terrain.session_save_load` is its soundness proof.
- **Harness caveats.** `holds` with `runs / 4` passes vacuously as "ok (0
  runs)" for small `--runs`. `refutes` fails spuriously with probability
  `(1-p)^runs`. If `minimise` hits its 5000-step cap the result is not a local
  minimum and nothing says so.
- **Shrinkers: no bug found.** Every candidate of every shrinker is strictly
  smaller under an explicit `Nat` measure (section 6), so none can loop, and
  for every property here the domain is the whole type, so none can leave it.
  Several leave the generator's *support*, harmlessly (`shrinkElapsed 14000`
  offers 7000; ray origins shrink to `y = 0`; `shrinkMesh` on 50 bytes offers
  26; after the `genEditY` change, `shrinkRenderOp` on `y = 31` offers 24).
- Minor: `genInventory` uses `for`/`let mut`, which basalt's `walk` has no rule
  for; `genSaveData` and `genRenderOp` bind local generators with `let`;
  `genSelect` draws a slot it may discard; `shrinkVec3` can offer the zero
  vector twice.

## 2. What basalt provides, and what it does not

`Gen` is not an opaque state monad. A generator is a term polymorphic in `G`
with `[Gen G]`, and `RandomChoice.choose` is the only source of randomness. The
same term is interpreted at `IO` (the C SplitMix `ioGen`), at `WordModel σ =
StateT σ Option` (PRNG state threaded purely), and at `SPMF`, the denotational
semantics, which has `SPMF.support`.

Provided (under `.lake/packages/basalt/Basalt/`):

- Laws (`Laws.lean`, `IO/Laws.lean`): `IsSoundFor`, `IsCompleteFor`,
  `IsSoundAndComplete`, `IsAlmostSurelyTerminating`, `IsCostBounded`,
  `IsFaithful`.
- Support lemmas (`SPMF/Support.lean`): `mem_support_bind_iff`, `support_pure`,
  `support_map`, the `ite`/`dite` forms, `support_frequency`,
  `mem_support_vectorOf_iff`, `mem_support_listOfMaxLength_iff`.
- The `walk` tactic with `mass_fixpoint` and `faithful_fixpoint`, with rules
  for `vectorOf`/`listOfMaxLength` and `@[gen_map]` lemmas for `chooseInt`,
  `elements` and `frequency!`.
- `SPMF.expect` / `SPMF.prob` for quantitative claims, `idealized_faithful`
  (the IO-to-SPMF bridge, assumptions spelled out), and `#genstats`.

Every generator in `Gen.lean` is non-recursive and built only from combinators
basalt has laws for, so an exact support characterisation is achievable for
each and no parallel theory is needed.

Not provided:

- **Shrinking.** No shrinker type, no laws. Sections 6 and 7 are new, plain
  list-and-arithmetic Lean.
- Named support lemmas for `chooseNat`, `chooseInt`, `elements` (their support
  is "what `walk` computes"); derive three once as a fallback.
- Anything for `forIn`, hence rewriting `genInventory` with `vectorOf`.
- A PRNG-independent soundness transfer: nothing says every output of a
  `WordModel σ` run lies in the `SPMF` support. Soundness reaches `IO` only
  through `IsFaithful` and the ideal-source reading.

What must be assumed about the PRNG (both inside `idealized_faithful`): that
the C `ioGen` matches the Lean SplitMix spec and no other thread uses it, and
that SplitMix's words are read as ideal i.i.d. uniform words. Completeness is
inherently a statement about that model.

## 3. What "correct" means here

**Generators.** For generator `g`, an honest target `T` (explicit bounds where
`g` is deliberately bounded) and the domain `D` of the theorem the property
restates:

- **G1, exact support**: `IsSoundAndComplete g T`. Applies to every generator.
- **G2, adequacy**: `T ⊆ D` (trivial here: `D` is everything), plus edge
  coverage: for each case class `E` the theorem's proof splits on,
  `∃ x, T x ∧ E x`. Structural classes are proved outright; behavioural
  classes over cheap pure functions (`ticksDue`, `dirtyChunks`, the floor check
  in `restore?`) are proved on a witness; classes that need the renderer or
  terrain evaluated stay as `refutes` self-checks (kernel evaluation is
  hopeless there and `native_decide` is against the repo's audit rule).
- **G3, link to what runs**: `IsAlmostSurelyTerminating g`, `IsFaithful g`.
- **G4, optional**: `SPMF.prob g E ≥ q` for the classes that matter. The only
  notion that would catch the "dig refused for lack of room" hole.

**Shrinkers.**

- **S1, decreasing**: `∀ y ∈ shrink x, size y < size x`. Applies to all.
- **S2, domain closure**: `D x → ∀ y ∈ shrink x, D y`. Trivial here; the
  stronger support closure is worth stating only for `shrinkList`.
- **S3, reachability**: `0` and `n - 1` are in `shrinkNat n`; every
  single-element deletion is in `shrinkList`. This gives one-minimality of
  list counterexamples and justifies `maxSize = 1` for `any`-shaped
  self-checks. Full shrink-completeness is false in general; not worth stating.

**Harness.** `holds` returning false: the reported value really fails and is
reachable by shrink steps from a generated sample. `holds` returning true:
every one of the `runs` samples passed, and nothing more. `refutes` returning
true: a failing input exists in the shrink-closure of the support with
`size ≤ maxSize`.

## 4. Order of work

0. **Refactor so each theorem is about the term that runs.** Name every
   generator handed to `holds`/`refutes` as a polymorphic `def` in `Gen.lean`
   (`genCommands n`, `genSeededCommands`, `genFrames`, `genRenderOps`,
   `genMutatedSave`, `genDecodeBytes`). Hoist `let`-bound generators
   (`genWideVec`, `genEdit`, `genEditCoord edge`, `genSeed`). Rewrite
   `genInventory` with `vectorOf 9 genStackSlot`. Split `Gen.lean` and
   `Shrink.lean` into a core-free half and a core-dependent half.
1. **Generic shrinkers and the harness** (core-free, Mathlib-free, no basalt
   semantics): `shrinkNat`, `shrinkInt`, `shrinkElapsed`, `shrinkList`,
   `shrinkPair`, `shrinkMesh`, the `Shrinker` bundle, a total `minimise`, the
   pure harness theorems.
2. **Core-free generator leaves**: three support lemmas, then `chance`,
   `genWideInt`, `genElapsed`, `genByte`, `genBytes`, `genMesh`, `genSlot`, the
   `listOfMaxLength` lift. First full basalt build happens here. Start with
   `genSpeed` and `genInput` as a spike of the `walk` recipe.
3. **Generators and shrinkers over core types**: `genSpeed`, `genLook`,
   `genInput`, `genBlock`, `genAnyBlock`, `genSelect`, `genSlot9`, `genChunk`,
   `genCentre`, `genEditY`, `genAction`, `genCommand`, `genRay`, `genFrame`,
   `genGpuCmd`, `genRenderOp`, `genInventory`, `genSaveData`, and their
   shrinkers.
4. **Coverage lemmas** (`Coverage.lean`), which mention `Session`, `SaveData`
   and `dirtyChunks`.
5. **Mechanical sweep**: `.terminates` and `.faithful` for every generator,
   then an axiom audit mirroring `LeanMc/Proofs/Audit.lean`.
6. **Optional**: quantitative bounds, detection probability, upstream basalt
   additions.

Where things live:

| Path under `proptest/` | Contents | Notes |
|---|---|---|
| `PropTest/Spec.lean` | Target predicates and size functions | Mathlib-free; give the predicates `Decidable` instances |
| `PropTest/Shrink/Basic.lean`, `PropTest/Shrink/Game.lean`, `PropTest/Harness.lean` | Shrinkers with their S1 proofs, total `minimise`, the pure harness | Must stay in the Mathlib-free `PropTest` lib: `Props.lean` and `Native.lean` consume the `Shrinker` bundle |
| `PropTestProofs/` (new `lean_lib`, default target) | `Support.lean`, `Gen/*.lean`, `Coverage.lean`, `Faithful.lean`, `Audit.lean` | Imports `Basalt`; must not be imported by the executables, so they do not link Mathlib |

With decidable spec predicates, add a `holds "samples satisfy their spec"`
property first and so test the soundness statements before proving them.

## 5. Generators: statements

Proof recipe for G1 (from basalt's `WORKFLOW.md`):

- Sound: `rw [IsSoundFor.iff_obs]; walk [callee.sound.obs, …]`, then
  `simp [Spec.…]; omega` per path.
- Complete: `intro x hx; unfold gen; rw [SPMF.mem_support_iff_may]; walk
  [callee.complete.obs, …]`, then pick the widest `frequency` branch and give
  one witness per draw.
- Always pass callee laws, or `walk` unfolds helpers and paths multiply.

Fallback lemmas:

```lean
theorem mem_support_chooseNat {lo hi n : Nat} (h : lo ≤ hi) :
    n ∈ SPMF.support (chooseNat lo hi h) ↔ lo ≤ n ∧ n ≤ hi
theorem mem_support_chooseInt {lo hi n : Int} (h : lo ≤ hi) :
    n ∈ SPMF.support (chooseInt lo hi h) ↔ lo ≤ n ∧ n ≤ hi
theorem mem_support_elements {xs : List α} {a : α} (h : xs ≠ []) :
    a ∈ SPMF.support (elements xs h) ↔ a ∈ xs
theorem listOfMaxLength.sound_complete {g : SPMF α} {P : α → Prop} (n : Nat)
    (h : IsSoundAndComplete g P) :
    IsSoundAndComplete (listOfMaxLength n g) fun xs => xs.length ≤ n ∧ ∀ x ∈ xs, P x
```

Targets, in `PropTest.Spec` (bounds as the generators stand now):

```lean
def Within (lo hi v : Int) : Prop := lo ≤ v ∧ v ≤ hi
def Cube (r : Int) (v : Vec3) : Prop := Within (-r) r v.x ∧ Within (-r) r v.y ∧ Within (-r) r v.z
def Speed (v : Int) : Prop := Within (-2000000) 2000000 v
def InputOK (i : Input) : Prop := Speed i.wishX ∧ Speed i.wishZ
def LookOK (v : Vec3) : Prop := Cube 9000000 v
def CommandOK (c : Command) : Prop := InputOK c.move ∧ LookOK c.look
def ElapsedOK (n : Nat) : Prop := n ≤ 450 ∨ (900 ≤ n ∧ n ≤ 200000)
def FrameOK (f : Frame) : Prop := InputOK f.move ∧ LookOK f.look ∧ ElapsedOK f.elapsed
def RayOK (r : Vec3 × Vec3) : Prop :=
  Within (-1310720) 1310720 r.1.x ∧ Within 557056 917504 r.1.y
    ∧ Within (-1310720) 1310720 r.1.z ∧ LookOK r.2
def Wide (n : Int) : Prop :=
  Within (-3000000) 3000000 n ∨ n ∈ [10^21, -10^21, 2^63, -(2^63) - 1]
def WideVec (v : Vec3) : Prop := Wide v.x ∧ Wide v.y ∧ Wide v.z
def SeedOK (s : UInt64) : Prop := s.toNat ≤ 100 ∨ s.toNat ∈ [2^64 - 1, 2^63, 2^32]
def SaveOK (d : SaveData) : Prop :=
  SeedOK d.seed ∧ WideVec d.player.pos ∧ WideVec d.player.vel ∧ d.edits.length ≤ 12
    ∧ ∀ e ∈ d.edits, Wide e.1.x ∧ Wide e.1.y ∧ Wide e.1.z
def ChunkOK (c : ChunkPos) : Prop := Within (-1) 1 c.x ∧ Within (-1) 1 c.y ∧ Within (-1) 1 c.z
def CentreOK (c : ChunkPos) : Prop := Within (-4) 4 c.x ∧ Within (-4) 4 c.y ∧ Within (-4) 4 c.z
def EditYOK (y : Int) : Prop := Within (-1) 17 y ∨ y = 31 ∨ y = 32
def EditOK (p : BlockPos) : Prop := Within (-20) 34 p.x ∧ EditYOK p.y ∧ Within (-20) 34 p.z
def RenderOpOK : RenderOp → Prop
  | .mesh c => ChunkOK c
  | .dropFar c => CentreOK c
  | .edit p _ => EditOK p
  | .draw e => Within (-2000000) 2000000 e.x ∧ Within 0 1000000 e.y ∧ Within (-2000000) 2000000 e.z
def MeshSize (n : Nat) : Prop := n ∈ [0, 1, 8, 23, 25, 47, 50, 24, 48, 72, 96, 120, 144]
def SlotOK (n : Nat) : Prop := n ≤ 5 ∨ n ∈ [16383, 16384, 16385, 70000, 4294967299]
def GpuCmdOK : GpuCmd → Prop
  | .upload s v => SlotOK s ∧ MeshSize v.size
  | .unload s => SlotOK s
  | .beginScene => True
  | .draw s o => SlotOK s ∧ Cube 4000000 o
```

`SaveOK` puts no constraint on soundness, as intended ("sound or not").

G1 statements (each at `G := SPMF`):

```lean
theorem chance.mem_support (p : Nat) (b : Bool) :
    b ∈ SPMF.support (chance p) ↔ (b = true ∧ 0 < p) ∨ (b = false ∧ p < 100)
theorem genSpeed.sound_complete     : IsSoundAndComplete genSpeed Spec.Speed
theorem genInput.sound_complete     : IsSoundAndComplete genInput Spec.InputOK
theorem genLook.sound_complete      : IsSoundAndComplete genLook Spec.LookOK
theorem genBlock.sound_complete     : IsSoundAndComplete genBlock fun _ => True
theorem genAnyBlock.sound_complete  : IsSoundAndComplete genAnyBlock fun _ => True
theorem genSelect.sound_complete    : IsSoundAndComplete genSelect fun _ => True
theorem genSlot9.sound_complete     : IsSoundAndComplete genSlot9 fun _ => True
theorem genAction.sound_complete    : IsSoundAndComplete genAction fun _ => True
theorem genCommand.sound_complete   : IsSoundAndComplete genCommand Spec.CommandOK
theorem genElapsed.sound_complete   : IsSoundAndComplete genElapsed Spec.ElapsedOK
theorem genFrame.sound_complete     : IsSoundAndComplete genFrame Spec.FrameOK
theorem genRay.sound_complete       : IsSoundAndComplete genRay Spec.RayOK
theorem genWideInt.sound_complete   : IsSoundAndComplete genWideInt Spec.Wide
theorem genInventory.sound_complete : IsSoundAndComplete genInventory fun _ => True
theorem genSaveData.sound_complete  : IsSoundAndComplete genSaveData Spec.SaveOK
theorem genChunk.sound_complete     : IsSoundAndComplete genChunk Spec.ChunkOK
theorem genCentre.sound_complete    : IsSoundAndComplete genCentre Spec.CentreOK
theorem genEditY.sound_complete     : IsSoundAndComplete genEditY Spec.EditYOK
theorem genRenderOp.sound_complete  : IsSoundAndComplete genRenderOp Spec.RenderOpOK
theorem genByte.sound_complete      : IsSoundAndComplete genByte fun _ => True
theorem genBytes.sound_complete (n : Nat) : IsSoundAndComplete (genBytes n) fun v => v.size = n
theorem genMesh.sound_complete      : IsSoundAndComplete genMesh fun v => Spec.MeshSize v.size
theorem genSlot.sound_complete      : IsSoundAndComplete genSlot Spec.SlotOK
theorem genGpuCmd.sound_complete    : IsSoundAndComplete genGpuCmd Spec.GpuCmdOK
theorem genMutatedSave.sound_complete : IsSoundAndComplete genMutatedSave fun ints =>
    ∃ d, Spec.SaveOK d ∧ ∃ j < d.encode.length, ∃ w, Spec.Wide w ∧ ints = d.encode.set j w
```

The call-site generators (`genCommands n`, `genFrames`, `genRenderOps`, …)
follow from `listOfMaxLength.sound_complete` in a line each.

| Generator | Completeness witness and lemmas | Difficulty |
|---|---|---|
| `chance` | `n = 0` for true, `n = 99` for false; `omega` | Easy |
| `genSpeed`, `genLook`, `genWideInt`, `genElapsed`, `genSlot`, `genChunk`, `genCentre`, `genEditY` | Widest branch covers the interval; `elements` branches by `simp`/`decide` | Easy, 10–25 lines each |
| `genBlock`, `genAnyBlock`, `genAction`, `genSlot9`, `genSelect`, `genByte` | `cases b <;> simp`; `Fin.ext`; `UInt8.ofNat_toNat` | Easy |
| `genInput`, `genCommand`, `genFrame`, `genRay`, `genGpuCmd`, `genRenderOp` | Pass callee laws; one `Or` branch per constructor | Easy to medium |
| `genBytes`, `genMesh` | Witness `b.data.toList`; dependent bind needs `fun n => (genBytes.sound_complete n).sound.obs` | Medium |
| `genInventory` | After the `vectorOf 9` rewrite: witness `inv.slots.toList`, then `Vector.ext`. With the `for` loop it is hard | Medium after rewrite |
| `genSaveData` | One witness per field; `UInt64.ofNat_toNat`; edits via the list lift | Medium |
| `genMutatedSave` | Needs `SaveData.length_encode : d.encode.length = 31 + 4 * d.edits.length` | Medium to hard |

G2 coverage statements (`PropTestProofs/Coverage.lean`), each a witness plus
completeness plus `decide`/`omega`:

```lean
-- Pacing: every tick count up to the cap, with any combination of presses.
-- `k = 1, dig = place = true` is the "dig first, place waits a tick" case.
theorem genFrame_covers_ticks (s : Session) (hs : s.debt < unitsPerTick) {k : Nat}
    (hk : k ≤ maxTicksPerFrame) (dig place fly : Bool) (sel : Option (Fin 9)) :
    ∃ f ∈ SPMF.support genFrame, s.ticksDue f = k ∧ f.dig = dig ∧ f.place = place
      ∧ f.fly = fly ∧ f.select = sel
theorem genFrame_covers_stall (s : Session) :
    ∃ f ∈ SPMF.support genFrame, maxTicksPerFrame < s.ticksOwed f

-- Look: zero, within reach, exactly at reach, beyond reach.
theorem genLook_covers_reach :
    (∃ v ∈ SPMF.support genLook, v = ⟨0, 0, 0⟩)
    ∧ (∃ v ∈ SPMF.support genLook, v.x.natAbs = 327680)
    ∧ (∃ v ∈ SPMF.support genLook, 327680 < v.x.natAbs)

-- Render: edges in every direction, and centres that make chunks far.
theorem genRenderOp_covers_edge :
    ∃ p b, RenderOp.edit p b ∈ SPMF.support genRenderOp ∧ (dirtyChunks p).length = 3
theorem genRenderOp_covers_vertical :
    ∃ p b, RenderOp.edit p b ∈ SPMF.support genRenderOp
      ∧ ∃ c ∈ dirtyChunks p, c.y ≠ p.chunkPos.y
theorem genRenderOp_covers_far (c : ChunkPos) (hc : Spec.ChunkOK c) :
    ∃ centre, RenderOp.dropFar centre ∈ SPMF.support genRenderOp
      ∧ (⟨1, 1⟩ : ViewRange).isFar centre c 1 = true

-- Save: saves that fail to load (edits := [(⟨0,0,0⟩, .stone)] fails the floor check).
theorem genSaveData_covers_unloadable :
    ∃ d ∈ SPMF.support genSaveData, d.restore? = none

-- Shim: every slot class, including the 32-bit alias of slot 3.
theorem genSlot_covers :
    ∀ n ∈ [0, 3, 16383, 16384, 4294967299], n ∈ SPMF.support genSlot
```

For the render lemmas go through the core's `mem_dirtyChunks` rather than
unfolding `eraseDups`. About 150 lines in all.

G3, per generator (about four lines each if `walk` cooperates):

```lean
theorem genFrame.terminates : IsAlmostSurelyTerminating genFrame := by
  mass_fixpoint [genInput.terminates.obs, …] using SPMF.LfpIsOne.one; simp
theorem genFrame.faithful : IsFaithful genFrame := by
  faithful_fixpoint [genFrame.terminates, genInput.faithful, …]
```

## 6. Shrinkers: statements

Bundle the measure with the shrinker, so a non-decreasing one cannot be passed
to `minimise`:

```lean
structure Shrinker (α : Type) where
  shrink : α → List α
  size : α → Nat
  decreasing : ∀ x, ∀ y ∈ shrink x, size y < size x

def Shrinker.none : Shrinker α
def Shrinker.pair (a : Shrinker α) (b : Shrinker β) : Shrinker (α × β)   -- sizes add
def Shrinker.list (s : Shrinker α) : Shrinker (List α)                   -- listSize s.size
```

Sizes:

```lean
def vecSize (v : Vec3) : Nat := v.x.natAbs + v.y.natAbs + v.z.natAbs
def blockSize (b : Block) : Nat := if b = .stone then 0 else 1
def selectSize : Option (Fin 9) → Nat | none => 0 | some i => i.val + 1
def inputSize (i : Input) : Nat :=
  i.toggleFly.toNat + i.jump.toNat + i.descend.toNat + i.wishX.natAbs + i.wishZ.natAbs
def commandSize (c : Command) : Nat :=
  c.action.isSome.toNat + selectSize c.select + inputSize c.move + vecSize c.look
def frameSize (f : Frame) : Nat :=
  f.dig.toNat + f.fly.toNat + f.place.toNat + selectSize f.select + f.elapsed
    + inputSize f.move + vecSize f.look
def listSize (size : α → Nat) (xs : List α) : Nat := (xs.map (size · + 1)).sum
def meshSize (v : ByteArray) : Nat := 2 * v.size + (if v.data.all (· == 0) then 0 else 1)
def slotSize : Option Stack → Nat | none => 0 | some s => 1 + s.extra.val + blockSize s.block
def inventorySize (inv : Inventory) : Nat := (inv.slots.toList.map slotSize).sum
def renderOpSize : RenderOp → Nat
  | .mesh c | .dropFar c => c.x.natAbs + c.y.natAbs + c.z.natAbs
  | .edit p b => p.x.natAbs + p.y.toNat + p.z.natAbs + blockSize b
  | .draw e => vecSize e
def gpuCmdSize : GpuCmd → Nat
  | .upload s v => s + meshSize v | .unload s => s | .beginScene => 0 | .draw s o => s + vecSize o
def saveSize (d : SaveData) : Nat :=
  listSize editSize d.edits + inventorySize d.inventory + playerSize d.player
    + d.seed.toNat + d.selected.val
```

`meshSize` avoids counting non-zero bytes: a shorter mesh loses at least 2,
and zeroing flips the flag.

Leaf lemmas:

```lean
theorem shrinkNat_lt {n m : Nat} (h : m ∈ shrinkNat n) : m < n
theorem zero_mem_shrinkNat {n : Nat} (h : 0 < n) : 0 ∈ shrinkNat n
theorem pred_mem_shrinkNat {n : Nat} (h : 0 < n) : n - 1 ∈ shrinkNat n
theorem shrinkInt_natAbs_lt {n m : Int} (h : m ∈ shrinkInt n) : m.natAbs < n.natAbs
theorem shrinkInt_between {n m : Int} (h : m ∈ shrinkInt n) :
    (0 ≤ n → 0 ≤ m ∧ m < n) ∧ (n ≤ 0 → n < m ∧ m ≤ 0)
theorem shrinkElapsed_lt {n m : Nat} (h : m ∈ shrinkElapsed n) : m < n
theorem shrinkList_lt (s : Shrinker α) {xs ys : List α} (h : ys ∈ shrinkList s.shrink xs) :
    listSize s.size ys < listSize s.size xs
theorem shrinkList_length_le {sh : α → List α} {xs ys : List α} (h : ys ∈ shrinkList sh xs) :
    ys.length ≤ xs.length
theorem shrinkList_forall {sh : α → List α} {P : α → Prop} (hP : ∀ x, P x → ∀ y ∈ sh x, P y)
    {xs ys : List α} (hx : ∀ x ∈ xs, P x) (h : ys ∈ shrinkList sh xs) : ∀ y ∈ ys, P y
theorem eraseIdx_mem_shrinkList (sh : α → List α) (xs : List α) {i : Nat} (hi : i < xs.length) :
    xs.eraseIdx i ∈ shrinkList sh xs
theorem shrinkMesh_lt {v w : ByteArray} (h : w ∈ shrinkMesh v) : meshSize w < meshSize v
theorem any_local_min_length {p : α → Bool} {xs : List α} (hx : xs.any p = true)
    (hmin : ∀ i < xs.length, (xs.eraseIdx i).any p = false) : xs.length = 1
```

The last, with `eraseIdx_mem_shrinkList`, proves `maxSize = 1` is always met
for `any`-shaped self-checks when the step cap is not hit.

The remaining S1 lemmas all have the form `y ∈ shrinkX x → xSize y < xSize x`,
for `shrinkVec3`, `shrinkChunk`, `shrinkBlock`, `shrinkSelect`, `shrinkInput`,
`shrinkCommand`, `shrinkFrame`, `shrinkPlayer`, `shrinkEdit`,
`shrinkInventory`, `shrinkRenderOp`, `shrinkGpuCmd`, `shrinkSaveData`.

| Shrinker | Approach | Difficulty |
|---|---|---|
| `shrinkNat`, `shrinkElapsed` | `List.mem_eraseDups`, `List.mem_filter` | Easy |
| `shrinkInt` | `natAbs` of `±m` | Easy |
| Record shrinkers | One macro: `simp only [shrinkX, List.mem_append, List.mem_map, …] at h; rcases h with …`, then `omega` with the component lemma | Easy, about 10 lines each |
| `shrinkList` | Each cut is `take (i*k) ++ drop ((i+1)*k)` with `i*k < n`, `0 < k`; `set` changes one summand | Medium, about 60 lines |
| `shrinkInventory` | Sum over `Vector.set`; `fin_cases i` with `omega` is the blunt option | Medium |
| `shrinkMesh` | `ByteArray.size_extract` | Medium |
| `shrinkRenderOp`, `shrinkGpuCmd` | Per constructor; `filterMap` membership | Easy to medium |
| `shrinkSaveData` | Composition; needs `n < d.seed.toNat → n.toUInt64.toNat = n` | Medium |

About 300 lines for S1 to S3.

## 7. Harness: statements

Make `minimise` total by structural recursion on fuel, generic in the monad so
the same code runs at `IO` and is reasoned about at `Id`:

```lean
def firstFailing [Monad m] (test : α → m (Option String)) : List α → m (Option (α × String))
  | [] => pure none
  | y :: ys => do
    match ← test y with
    | some msg => pure (some (y, msg))
    | none => firstFailing test ys

def minimise [Monad m] (shrink : α → List α) (test : α → m (Option String)) :
    Nat → α → String → Nat → m (α × String × Nat)
  | 0, x, msg, steps => pure (x, msg, steps)
  | fuel + 1, x, msg, steps => do
    match ← firstFailing test (shrink x) with
    | some (y, msg') => minimise shrink test fuel y msg' (steps + 1)
    | none => pure (x, msg, steps)

inductive Reaches (shrink : α → List α) : α → α → Prop
  | refl : Reaches shrink x x
  | step : y ∈ shrink x → Reaches shrink y z → Reaches shrink x z

theorem minimise_spec (s : Shrinker α) (t : α → Option String) (fuel : Nat) {x : α} {msg : String}
    (hx : t x = some msg) :
    let r := Id.run (minimise s.shrink (fun a => pure (t a)) fuel x msg 0)
    t r.1 = some r.2.1 ∧ Reaches s.shrink x r.1 ∧ r.2.2 ≤ fuel
      ∧ s.size r.1 + r.2.2 ≤ s.size x
      ∧ (r.2.2 < fuel → ∀ y ∈ s.shrink r.1, t y = none)

theorem Reaches.domain {shrink : α → List α} {D : α → Prop}
    (hD : ∀ x, D x → ∀ y ∈ shrink x, D y) {x y : α} (hx : D x) (h : Reaches shrink x y) : D y
```

Fuel alone gives totality; the measure gives the meaning: with
`fuel := s.size x + 1` the loop always stops at a local minimum, so the 5000
cap becomes an explicit time budget. Report it when it is the reason for
stopping.

Rewrite `findCounterexample` as structural recursion on `runs`, and split
`holds`/`refutes` into a pure verdict plus printing:

```lean
def samples (gen : StateM σ α) : Nat → σ → List α
  | 0, _ => []
  | n + 1, st => (gen.run st).1 :: samples gen n (gen.run st).2

theorem findCounterexample_none_iff (gen : StateM σ α) (s : Shrinker α) (t : α → Option String)
    (runs : Nat) (st : σ) :
    ((findCounterexample runs gen s (fun a => pure (t a))).run st).1 = none
      ↔ ∀ x ∈ samples gen runs st, t x = none

theorem findCounterexample_some (gen : StateM σ α) (s : Shrinker α) (t : α → Option String)
    (runs : Nat) (st : σ) {x' : α} {msg : String} {run steps : Nat}
    (h : ((findCounterexample runs gen s (fun a => pure (t a))).run st).1
          = some (x', msg, run, steps)) :
    t x' = some msg ∧ ∃ x, (samples gen runs st)[run - 1]? = some x ∧ Reaches s.shrink x x'
```

About 150 lines, mostly `StateT.run_bind` bookkeeping. These hold for the
harness at a pure state monad; that `IO` runs the same thing is the trust
basalt already names. For `Native.lean`, whose test reads the real shim, there
is no theorem beyond "a reported value failed when it was tested".

Optional: with the sample loop written over `[Gen G]`, at `SPMF` the
probability that `n` runs all pass is `(1 - SPMF.prob gen {x | t x ≠ none})^n`.
The qualitative half is cheap from G1 and basalt's `expect_pos_iff`: detection
has positive probability exactly when some `x` with `T x` fails.

## 8. Risks

- **`walk` on these terms is untested.** Risk points are nested `(← g)` inside
  structure literals, the `frequency!` desugaring, and the names of leftover
  goals. The three support lemmas plus `simp` are the fallback.
- **First build cost.** The proofs lib will compile basalt's `SPMF`, `Walk`
  and `Tactic` modules on first use.
- **Soundness at `IO` is only as strong as the idealisation**, unless a
  `WordModel`-level relation is added upstream (a `GenRel (WordModel σ) SPMF`
  for `fun x y => ∀ s a s', x.run s = some (a, s') → a ∈ y.support`).
- **Support-level coverage is qualitative.** A case can be in the support and
  never happen; for such classes use `refutes` self-checks or G4 bounds.
