# The property-test generators, proved

`lake build` in this directory checks proofs that every generator the
property tests run is correct. This file says what is proved, what the proofs
rest on, what is proved of the shrinkers, and what is proposed but not yet
done for the harness.

## What is proved

For each of the 44 generators in `PropTest/Gen.lean`, in `PropTestProofs/`:

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
| `Basic.lean` | `chance`, `genSpeed`, `genInput`, `genLook`, `genBlock`, `genAnyBlock`, `genSelect`, `genSlot9`, `genHeading`, `genAction`, `genElapsed`, `genWideInt` |
| `Game.lean` | `genCommand`, `genCommands`, `genSeededCommands`, `genFrame`, `genFrames`, `genRay` |
| `Render.lean` | `genChunk`, `genCentre`, `genEditY`, `genEditCoord`, `genEditPos`, `genRenderOp`, `genRenderOps`, `genClientRun` |
| `Gpu.lean` | `genByte`, `genBytes`, `genMesh`, `genSlot`, `genGpuCmd`, `genGpuCmds`, `genLongScene`, `genDecodeBytes` |
| `Save.lean` | `genStackSlot`, `genInventory`, `genWideVec`, `genSeed`, `genEdit`, `genPlayer`, `genEntity`, `genColumn`, `genSaveData`, `genMutatedSave` |

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
- `genLongScene_covers_log`: a scene one draw short of filling the shim's draw
  log, one that exactly fills it, and one a draw too long for it.
- `genSaveData_covers_unloadable`, `_loadable`: a save that is refused and a
  save that loads.
- `genSaveData_covers_fox`, `_unsound_fox`: a save with a fox that loads, and
  a save that is refused for its fox alone.

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

## The shrinkers

basalt has laws for generators and none for shrinkers, so what a shrinker
should satisfy is a choice. One law is proved, in `PropTestProofs/Shrink.lean`,
and two more are discussed below it.

**Decreasing** (proved, of every shrinker). Every candidate is strictly
smaller than its input under an explicit measure, a natural number:

```lean
def Decreasing (shrink : α → List α) (size : α → Nat) : Prop :=
  ∀ x, ∀ y ∈ shrink x, size y < size x
```

The file gives a measure for each shrinker (`commandSize`, `frameSize`,
`renderOpSize`, `meshSize`, `gpuCmdSize`, `inventorySize`, `entitySize`,
`columnSize`, `saveSize`, and `listSize` for lists) and proves the law for each: `shrinkNat`,
`shrinkInt`, `shrinkElapsed`, `shrinkVec3`, `shrinkSelect`, `shrinkBlock`,
`shrinkInput`, `shrinkCommand`, `shrinkFrame`, `shrinkChunk`, `shrinkRenderOp`,
`shrinkMesh`, `shrinkGpuCmd`, `shrinkInventory`, `shrinkPlayer`,
`shrinkEntity`, `shrinkEdit`, `shrinkSaveData`, and the combinators `shrinkList` and `shrinkPair` for any
decreasing shrinker of their elements. Its last section instantiates these at
exactly the shrinkers `Props.lean` and `Native.lean` hand to `minimise`,
among them the pairs that shrink a client's run and a long scene.

What it buys is `Decreasing.steps_le`: a chain of shrink steps from `x` is at
most `size x` long. So shrinking stops by itself, and the 5000-step cap in
`minimise` is a budget of time, never what stands between it and a loop.

Nothing enforces that a new shrinker comes with its proof. Bundling the
measure with the shrinker would:

```lean
structure Shrinker (α : Type) where
  shrink : α → List α
  size : α → Nat
  decreasing : Decreasing shrink size
```

That means moving the measures and their proofs into the Mathlib-free
`PropTest` library, which the test executables link; none of the proofs needs
Mathlib.

**Closed** (not asked for). Every candidate is still a value the generator
could have produced. It holds of the command shrinker
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
