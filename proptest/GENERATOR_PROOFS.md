# The property-test generators, proved

`lake build` in this directory checks proofs that every generator the
property tests run is correct. This file says what is proved, what the proofs
rest on, and what is proposed but not yet done: the shrinkers and the harness.

## What is proved

For each of the 39 generators in `PropTest/Gen.lean`, in `PropTestProofs/`:

| Law | Meaning | Name |
|---|---|---|
| Sound and complete | The values it can produce are exactly those its predicate in `PropTest/Spec.lean` allows: nothing outside, and nothing inside left out | `<gen>.sound_complete` |
| Terminates | It returns with probability one | `<gen>.terminates` |
| Faithful | Run on an ideal source of random words it has exactly the distribution the other laws are about, and `IO` does what that model does | `<gen>.faithful` |
| Cost bounded | It makes at most a stated number of random choices, as a function of the value produced; so no generator retries or discards a draw | `<gen>.cost_bounded` |

The laws are basalt's (`Basalt/Laws.lean`, `Basalt/IO/Laws.lean`), and every
proof is one `walk` over the generator's definition followed by arithmetic.

| File | Generators |
|---|---|
| `Basic.lean` | `chance`, `genSpeed`, `genInput`, `genLook`, `genBlock`, `genAnyBlock`, `genSelect`, `genSlot9`, `genAction`, `genElapsed`, `genWideInt` |
| `Game.lean` | `genCommand`, `genCommands`, `genSeededCommands`, `genFrame`, `genFrames`, `genRay` |
| `Render.lean` | `genChunk`, `genCentre`, `genEditY`, `genEditCoord`, `genEditPos`, `genRenderOp`, `genRenderOps` |
| `Gpu.lean` | `genByte`, `genBytes`, `genMesh`, `genSlot`, `genGpuCmd`, `genGpuCmds`, `genDecodeBytes` |
| `Save.lean` | `genStackSlot`, `genInventory`, `genWideVec`, `genSeed`, `genEdit`, `genPlayer`, `genSaveData`, `genMutatedSave` |

So that each theorem is about the term that runs, every generator a property
uses is a named definition, with none bound locally inside another. The
refactor that made them so draws the same random numbers in the same order:
the tests' output for a fixed seed is unchanged.

`Coverage.lean` then shows the generators reach the cases the game's theorems
treat separately. Each is a consequence of completeness: a value in the
predicate that has the case.

- `genFrame_covers_ticks`: every number of ticks up to the per-frame limit,
  with every combination of presses. One tick with a dig and a place together
  is the case where the place waits.
- `genFrame_covers_stall`: a frame that owes more ticks than it may run.
- `genCommand_covers_actions`, `genLook_covers_reach`: every action with every
  slot choice; looks within the reach, and looks cut down to it.
- `genRenderOp_covers_corner`, `_vertical`, `_far`: an edit touching three
  chunks, an edit touching the chunk above, and a view centre that puts any
  meshed chunk out of view.
- `genSlot_covers`, `genGpuCmd_covers_misuse`: every kind of slot, and each
  misuse the shim's model calls a fault.
- `genSaveData_covers_unloadable`, `_loadable`: a save that is refused and a
  save that loads.

`Audit.lean` checks that every theorem here rests on Lean's three standard
axioms only, and fails if a proof file in the directory is not imported.

The predicates are decidable, so `Props.lean` also runs "every generator
draws only what it is proved to produce" against the real random source.

## What the proofs rest on

Soundness and completeness are statements about `SPMF`, the distribution a
generator denotes. `faithful` connects that to what runs, under two things
basalt names in `idealized_faithful` and Lean cannot decide:

- the C `ioGen` matches the Lean SplitMix specification, and nothing else uses
  it during a run;
- SplitMix's words are read as ideal, independent and uniform. This is a
  model, like the random-oracle model, not a hypothesis: with `2^64` seeds
  most of a 150-command list's support is unreachable from any real seed.

Completeness is therefore a statement about that model. The runtime check in
`Props.lean` is the test of the first assumption on this code.

A case can also be in a generator's support and never be drawn. These proofs
cannot see that; the `refutes` self-checks in `Props.lean` are what show a
case is actually found.

## Found on the way, and still open

- **A dig refused for lack of room is effectively unreachable** in the command
  properties: it is in the support but needs about 130 well-aimed digs in at
  most 150 commands. A second start state with a full inventory, and a
  `refutes` "a dig can be refused for lack of room", would close it.
  `Tests.lean` covers the case directly.
- **Loadable saves are rare** from `genSaveData`: well under 1% of draws pass
  `restore?`. No property needs one. If one is added, generate saves that are
  sound by construction: play frames from `Terrain.session seed` and take
  `.snapshot`; `Terrain.session_save_load` is its soundness proof.
- **`holds` with `runs / 4` passes vacuously** as "ok (0 runs)" for small
  `--runs`, and `refutes` fails spuriously with probability `(1-p)^runs`.

## Proposed: the shrinkers

basalt has laws for generators and none for shrinkers, so what a shrinker
should satisfy is a choice. `PropTestProofs/Shrink.lean` works the two
candidate laws through for the command shrinker, as something concrete to
decide on.

**Decreasing** (recommended; proved for `shrinkNat`, `shrinkInt`,
`shrinkElapsed`, `shrinkVec3`, `shrinkSelect`, `shrinkInput`,
`shrinkCommand`). Every candidate is strictly smaller than its input under an
explicit measure:

```lean
theorem shrinkCommand_lt {c d : Command} (h : d ∈ shrinkCommand c) :
    commandSize d < commandSize c
```

This is what makes `minimise` stop without a step cap. It holds of every
shrinker here. The measures for the rest:

```lean
def blockSize (b : Block) : Nat := if b = .stone then 0 else 1
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
and zeroing flips the flag. `shrinkList` is the one with real content, about
60 lines: each cut is `take (i*k) ++ drop ((i+1)*k)` with `i*k < n` and
`0 < k`, and `set` changes one summand.

To make the law impossible to forget, bundle the measure with the shrinker:

```lean
structure Shrinker (α : Type) where
  shrink : α → List α
  size : α → Nat
  decreasing : ∀ x, ∀ y ∈ shrink x, size y < size x
```

**Closed** (not recommended as a requirement). Every candidate is still a
value the generator could have produced. It holds of the command shrinker
(`shrinkCommand_ok`, `shrinkCommand_support`), because every range it draws
from contains zero. It is false of the frame shrinker
(`shrinkElapsed_not_closed`: 900 shrinks to 899, in the gap the generator
leaves between half a tick and nine tenths of one), and for the same reason of
the ray, renderer, shim and save shrinkers. No property here needs it: each
restates a theorem about every input, so a counterexample outside the
generator's reach is still a counterexample. If a property ever assumes its
generator's predicate, the predicates are decidable, and filtering a
shrinker's candidates by one makes it closed by construction.

**Reaching** (cheap, optional). `0` and `n - 1` are in `shrinkNat n`, and
every single-element deletion is in `shrinkList`:

```lean
theorem eraseIdx_mem_shrinkList (sh : α → List α) (xs : List α) {i : Nat} (hi : i < xs.length) :
    xs.eraseIdx i ∈ shrinkList sh xs
theorem any_local_min_length {p : α → Bool} {xs : List α} (hx : xs.any p = true)
    (hmin : ∀ i < xs.length, (xs.eraseIdx i).any p = false) : xs.length = 1
```

Together these justify `maxSize = 1` for the `any`-shaped self-checks. That
greedy shrinking finds a global minimum is false in general and not worth
stating.

## Proposed: the harness

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
```

Fuel alone gives totality; the measure gives the meaning: with
`fuel := s.size x + 1` the loop always stops at a local minimum, so the 5000
cap becomes an explicit time budget, to be reported when it is the reason for
stopping. `holds` returning false then means the reported value really fails
and is reachable by shrink steps from a generated sample; `holds` returning
true means each of the `runs` samples passed, and nothing more. About 150
lines, mostly `StateT.run_bind` bookkeeping. For `Native.lean`, whose test
reads the real shim, there is no theorem beyond "a reported value failed when
it was tested".

Optional and harder: at `SPMF`, the probability that `n` runs all pass is
`(1 - SPMF.prob gen {x | t x ≠ none})^n`. The qualitative half is cheap from
the support laws: detection has positive probability exactly when some value
in the generator's predicate fails.
