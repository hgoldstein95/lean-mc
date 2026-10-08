import PropTest.Gen
import Basalt.PBT.Campaign

/-!
# Shrinkers and the test runner

basalt generates; shrinking is done here by hand. A shrinker lists inputs that
are smaller than the one it is given, most drastic first, and `minimise` keeps
taking the first one that still fails. So generators can be as wide as they
like and a failure is still reported small.
-/

open LeanMc

namespace PropTest

/-! ## Shrinkers -/

/--
Smaller numbers: zero, then values that close half, three quarters, seven
eighths... of the distance from zero to `n`, ending just short of `n`. Taking
the first that still fails homes in on the smallest failing value in a number
of steps logarithmic in `n`, not linear.
-/
def shrinkNat (n : Nat) : List Nat :=
  let gaps := (List.range 64).map (fun k => n / 2 ^ (k + 1)) |>.takeWhile (0 < ·)
  ((0 :: gaps.map (n - ·)) ++ [n - 1]).filter (· < n) |>.eraseDups

def shrinkInt (n : Int) : List Int :=
  (shrinkNat n.natAbs).map fun (m : Nat) => if n < 0 then -Int.ofNat m else Int.ofNat m

/-- Frame times also shrink towards a whole number of ticks. -/
def shrinkElapsed (n : Nat) : List Nat :=
  ([0, n / 1000 * 1000, n / 2, n - 1].filter (· < n)).eraseDups

def shrinkVec3 (v : Vec3) : List Vec3 :=
  (if v = ⟨0, 0, 0⟩ then [] else [(⟨0, 0, 0⟩ : Vec3)])
    ++ (shrinkInt v.x).map (fun x => { v with x })
    ++ (shrinkInt v.y).map (fun y => { v with y })
    ++ (shrinkInt v.z).map (fun z => { v with z })

def shrinkBlock (b : Block) : List Block :=
  if b = .stone then [] else [.stone]

def shrinkInput (i : Input) : List Input :=
  (if i.toggleFly then [{ i with toggleFly := false }] else [])
    ++ (if i.jump then [{ i with jump := false }] else [])
    ++ (if i.descend then [{ i with descend := false }] else [])
    ++ (shrinkInt i.wishX).map (fun x => { i with wishX := x })
    ++ (shrinkInt i.wishZ).map (fun z => { i with wishZ := z })

def shrinkPlace : Option Block → List (Option Block)
  | none => []
  | some b => none :: (shrinkBlock b).map some

def shrinkCommand (c : Command) : List Command :=
  (if c.dig then [{ c with dig := false }] else [])
    ++ (shrinkPlace c.place).map (fun place => { c with place })
    ++ (shrinkInput c.move).map (fun move => { c with move })
    ++ (shrinkVec3 c.look).map (fun look => { c with look })

def shrinkFrame (f : Frame) : List Frame :=
  (if f.dig then [{ f with dig := false }] else [])
    ++ (if f.fly then [{ f with fly := false }] else [])
    ++ (shrinkPlace f.place).map (fun place => { f with place })
    ++ (shrinkElapsed f.elapsed).map (fun elapsed => { f with elapsed })
    ++ (shrinkInput f.move).map (fun move => { f with move })
    ++ (shrinkVec3 f.look).map (fun look => { f with look })

def shrinkChunk (c : ChunkPos) : List ChunkPos :=
  (if c = ⟨0, 0, 0⟩ then [] else [(⟨0, 0, 0⟩ : ChunkPos)])
    ++ (shrinkInt c.x).map (fun x => { c with x })
    ++ (shrinkInt c.y).map (fun y => { c with y })
    ++ (shrinkInt c.z).map (fun z => { c with z })

def shrinkRenderOp : RenderOp → List RenderOp
  | .mesh c => (shrinkChunk c).map .mesh
  | .edit p b =>
    (shrinkBlock b).map (.edit p ·)
      ++ (shrinkInt p.x).map (fun x => .edit { p with x } b)
      ++ (shrinkInt p.z).map (fun z => .edit { p with z } b)
      ++ (shrinkNat p.y.toNat).filterMap (fun y => if y = 0 then none else some (.edit { p with y } b))
  | .dropFar c => (shrinkChunk c).map .dropFar
  | .draw eye => (shrinkVec3 eye).map .draw

/-- A mesh shrinks by losing triangles, then by its bytes going to zero. -/
def shrinkMesh (v : ByteArray) : List ByteArray :=
  let shorter := ([0, v.size / 48 * 24, v.size - 24].filter (· < v.size)).eraseDups.map fun n => v.extract 0 n
  let zeroed := if v.data.all (· == 0) then [] else [ByteArray.mk (v.data.map fun _ => 0)]
  shorter ++ zeroed

def shrinkGpuCmd : GpuCmd → List GpuCmd
  | .upload slot v =>
    (shrinkNat slot).filterMap (fun s => if s = 0 then none else some (.upload s v))
      ++ (shrinkMesh v).map (.upload slot ·)
  | .unload slot => (shrinkNat slot).filterMap (fun s => if s = 0 then none else some (.unload s))
  | .beginScene => []
  | .draw slot offset =>
    (shrinkNat slot).filterMap (fun s => if s = 0 then none else some (.draw s offset))
      ++ (shrinkVec3 offset).map (.draw slot ·)

/--
Smaller lists: first with a half, quarter or eighth cut out, then with one
element removed, then with one element made smaller.
-/
def shrinkList (shrinkElem : α → List α) (xs : List α) : List (List α) :=
  let n := xs.length
  let cut (k : Nat) : List (List α) :=
    (List.range ((n + k - 1) / k)).map fun i => xs.take (i * k) ++ xs.drop ((i + 1) * k)
  let sizes := ([n / 2, n / 4, n / 8, 1].filter fun k => 0 < k ∧ k ≤ n).eraseDups
  sizes.flatMap cut
    ++ (List.range n).flatMap fun i =>
      match xs[i]? with
      | some x => (shrinkElem x).map fun y => xs.set i y
      | none => []

def shrinkPair (shrinkA : α → List α) (shrinkB : β → List β) (p : α × β) : List (α × β) :=
  (shrinkA p.1).map (·, p.2) ++ (shrinkB p.2).map (p.1, ·)

/-! ## Running a property -/

/-- Shrink a failing input: keep taking the first smaller input that still fails. -/
partial def minimise (shrink : α → List α) (test : α → IO (Option String)) (x : α)
    (message : String) (steps : Nat := 0) : IO (α × String × Nat) := do
  if steps ≥ 5000 then return (x, message, steps)
  for y in shrink x do
    if let some message' ← test y then
      return ← minimise shrink test y message' (steps + 1)
  return (x, message, steps)

/--
Test `test` on `runs` generated inputs. `test` returns a description of what
went wrong, or `none`. On a failure, the input is shrunk and returned.
-/
def findCounterexample (runs : Nat) (gen : IO α) (shrink : α → List α)
    (test : α → IO (Option String)) : IO (Option (α × String × Nat × Nat)) := do
  for i in [0:runs] do
    let x ← gen
    if let some message ← test x then
      let (x', message', steps) ← minimise shrink test x message
      return some (x', message', i + 1, steps)
  return none

/-- Run a property that should hold. Reports and returns whether it did. -/
def holds (name : String) (runs : Nat) (gen : IO α) (shrink : α → List α) (render : α → String)
    (test : α → IO (Option String)) : IO Bool := do
  match ← findCounterexample runs gen shrink test with
  | none =>
    IO.println s!"ok    {name} ({runs} runs)"
    return true
  | some (x, message, run, steps) =>
    IO.println s!"FAIL  {name}"
    Basalt.PBT.reportFailure (render x)
      #[("failure", message), ("found", s!"on run {run}, shrunk in {steps} steps")]
    return false

/--
Run a property that is known to be false, as a check on the tests themselves:
the generator must find a counterexample, and the shrinker must bring it down
to at most `maxSize`.
-/
def refutes (name : String) (runs : Nat) (gen : IO α) (shrink : α → List α) (size : α → Nat)
    (maxSize : Nat) (render : α → String) (test : α → IO (Option String)) : IO Bool := do
  match ← findCounterexample runs gen shrink test with
  | none =>
    IO.println s!"FAIL  {name}: no counterexample found in {runs} runs"
    return false
  | some (x, _, run, steps) =>
    if size x ≤ maxSize then
      IO.println s!"ok    {name} (found on run {run}, shrunk in {steps} steps to: {render x})"
      return true
    else
      IO.println s!"FAIL  {name}: shrunk only to size {size x}, wanted at most {maxSize}"
      IO.println s!"      {render x}"
      return false

end PropTest
