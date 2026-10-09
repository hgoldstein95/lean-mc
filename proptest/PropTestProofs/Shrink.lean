import PropTestProofs.Game
import PropTest.Shrink

/-!
# What could be proved of the shrinkers: a worked proposal

basalt has laws for generators and none for shrinkers, so what a shrinker
should satisfy is a choice. This file works the two candidate laws through for
one pipeline, the one that shrinks commands, so that the choice can be made on
something concrete.

**Decreasing.** Every candidate a shrinker offers is strictly smaller than its
input under an explicit measure. This is what makes "keep taking the first
candidate that still fails" stop, without a cap on the number of steps. It
holds of every shrinker in `PropTest.Shrink`; it is proved here for numbers,
vectors, inputs, slot choices and commands.

**Closed.** Every candidate is still a value the generator could have
produced. This is what would let a property assume its generator's predicate
and still trust a shrunk counterexample. It holds of the command shrinker,
proved below, because every range it draws from contains zero. It is false of
the frame shrinker, also shown below, and of the ray, renderer, shim and save
shrinkers for the same reason: they shrink into gaps the generator leaves on
purpose. No property here needs it, since each restates a theorem about every
input, so a counterexample outside the generator's reach is still one.
-/

open LeanMc PropTest

namespace PropTest

/-! ## Decreasing -/

theorem shrinkNat_lt {n m : Nat} (h : m ∈ shrinkNat n) : m < n :=
  of_decide_eq_true (List.mem_filter.mp (List.mem_eraseDups.mp h)).2

theorem shrinkElapsed_lt {n m : Nat} (h : m ∈ shrinkElapsed n) : m < n :=
  of_decide_eq_true (List.mem_filter.mp (List.mem_eraseDups.mp h)).2

/-- A shrunk integer is nearer zero, on the same side of it. -/
theorem shrinkInt_between {n m : Int} (h : m ∈ shrinkInt n) :
    (0 ≤ n → 0 ≤ m ∧ m < n) ∧ (n ≤ 0 → n < m ∧ m ≤ 0) := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
  have := shrinkNat_lt hk
  simp only [Int.ofNat_eq_natCast]
  split <;> omega

theorem shrinkInt_natAbs_lt {n m : Int} (h : m ∈ shrinkInt n) : m.natAbs < n.natAbs := by
  have := shrinkInt_between h
  omega

/-- The size of a vector for shrinking: how far its components are from zero, in all. -/
def vecSize (v : Vec3) : Nat :=
  v.x.natAbs + v.y.natAbs + v.z.natAbs

theorem shrinkVec3_lt {v w : Vec3} (h : w ∈ shrinkVec3 v) : vecSize w < vecSize v := by
  simp only [shrinkVec3, List.mem_append, List.mem_map] at h
  rcases h with ((h | ⟨x, hx, rfl⟩) | ⟨y, hy, rfl⟩) | ⟨z, hz, rfl⟩
  · split at h
    · cases h
    · next hne =>
      simp only [List.mem_singleton] at h
      subst h
      have : v.x ≠ 0 ∨ v.y ≠ 0 ∨ v.z ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hne (Vec3.ext hc.1 hc.2.1 hc.2.2)
      simp only [vecSize]
      omega
  · have := shrinkInt_natAbs_lt hx
    simp only [vecSize]
    omega
  · have := shrinkInt_natAbs_lt hy
    simp only [vecSize]
    omega
  · have := shrinkInt_natAbs_lt hz
    simp only [vecSize]
    omega

def selectSize : Option (Fin 9) → Nat
  | none => 0
  | some i => i.val + 1

theorem shrinkSelect_lt {s t : Option (Fin 9)} (h : t ∈ shrinkSelect s) :
    selectSize t < selectSize s := by
  cases s with
  | none => cases h
  | some i =>
    simp only [shrinkSelect, List.mem_cons] at h
    rcases h with rfl | h
    · simp [selectSize]
    · split at h
      · cases h
      · next hi =>
        simp only [List.mem_singleton] at h
        subst h
        have : i.val ≠ 0 := fun e => hi (Fin.ext e)
        simp only [selectSize, Fin.val_zero]
        omega

def inputSize (i : Input) : Nat :=
  i.toggleFly.toNat + i.jump.toNat + i.descend.toNat + i.wishX.natAbs + i.wishZ.natAbs

theorem shrinkInput_lt {i j : Input} (h : j ∈ shrinkInput i) : inputSize j < inputSize i := by
  simp only [shrinkInput, List.mem_append, List.mem_map] at h
  rcases h with (((h | h) | h) | ⟨x, hx, rfl⟩) | ⟨z, hz, rfl⟩
  · split at h
    · next ht =>
      simp only [List.mem_singleton] at h
      subst h
      simp [inputSize, ht]
    · cases h
  · split at h
    · next ht =>
      simp only [List.mem_singleton] at h
      subst h
      simp [inputSize, ht]
    · cases h
  · split at h
    · next ht =>
      simp only [List.mem_singleton] at h
      subst h
      simp [inputSize, ht]
    · cases h
  · have := shrinkInt_natAbs_lt hx
    simp only [inputSize]
    omega
  · have := shrinkInt_natAbs_lt hz
    simp only [inputSize]
    omega

def commandSize (c : Command) : Nat :=
  c.action.isSome.toNat + selectSize c.select + inputSize c.move + vecSize c.look

/--
**The command shrinker is decreasing.** Every candidate it offers is strictly
smaller, so shrinking a command stops, after at most `commandSize c` steps.
-/
theorem shrinkCommand_lt {c d : Command} (h : d ∈ shrinkCommand c) :
    commandSize d < commandSize c := by
  simp only [shrinkCommand, List.mem_append, List.mem_map] at h
  rcases h with ((h | ⟨s, hs, rfl⟩) | ⟨m, hm, rfl⟩) | ⟨l, hl, rfl⟩
  · split at h
    · next ha =>
      simp only [List.mem_singleton] at h
      subst h
      simp [commandSize, ha]
    · cases h
  · have := shrinkSelect_lt hs
    simp only [commandSize]
    omega
  · have := shrinkInput_lt hm
    simp only [commandSize]
    omega
  · have := shrinkVec3_lt hl
    simp only [commandSize]
    omega

/-! ## Closed -/

/-- Shrinking a vector inside a cube about the origin leaves it inside the cube. -/
theorem shrinkVec3_cube {r : Int} {v w : Vec3} (hv : Spec.Cube r v) (h : w ∈ shrinkVec3 v) :
    Spec.Cube r w := by
  simp only [Spec.Cube, Spec.Within] at hv ⊢
  simp only [shrinkVec3, List.mem_append, List.mem_map] at h
  rcases h with ((h | ⟨x, hx, rfl⟩) | ⟨y, hy, rfl⟩) | ⟨z, hz, rfl⟩
  · split at h
    · cases h
    · simp only [List.mem_singleton] at h
      subst h
      dsimp only
      omega
  · have := shrinkInt_between hx
    dsimp only
    omega
  · have := shrinkInt_between hy
    dsimp only
    omega
  · have := shrinkInt_between hz
    dsimp only
    omega

theorem shrinkInput_ok {i j : Input} (hi : Spec.InputOK i) (h : j ∈ shrinkInput i) :
    Spec.InputOK j := by
  simp only [Spec.InputOK, Spec.Speed, Spec.Within] at hi ⊢
  simp only [shrinkInput, List.mem_append, List.mem_map] at h
  rcases h with (((h | h) | h) | ⟨x, hx, rfl⟩) | ⟨z, hz, rfl⟩
  · split at h
    · simp only [List.mem_singleton] at h
      subst h
      exact hi
    · cases h
  · split at h
    · simp only [List.mem_singleton] at h
      subst h
      exact hi
    · cases h
  · split at h
    · simp only [List.mem_singleton] at h
      subst h
      exact hi
    · cases h
  · have := shrinkInt_between hx
    dsimp only
    omega
  · have := shrinkInt_between hz
    dsimp only
    omega

/--
**The command shrinker is closed.** Shrinking a command the generator can
produce gives only commands the generator can produce.
-/
theorem shrinkCommand_ok {c d : Command} (hc : Spec.CommandOK c) (h : d ∈ shrinkCommand c) :
    Spec.CommandOK d := by
  simp only [shrinkCommand, List.mem_append, List.mem_map] at h
  rcases h with ((h | ⟨s, hs, rfl⟩) | ⟨m, hm, rfl⟩) | ⟨l, hl, rfl⟩
  · split at h
    · simp only [List.mem_singleton] at h
      subst h
      exact hc
    · cases h
  · exact hc
  · exact ⟨shrinkInput_ok hc.1 hm, hc.2⟩
  · exact ⟨hc.1, shrinkVec3_cube hc.2 hl⟩

/-- So a shrunk command is one the command generator could have drawn. -/
theorem shrinkCommand_support {c d : Command} (hc : c ∈ SPMF.support genCommand)
    (h : d ∈ shrinkCommand c) : d ∈ SPMF.support genCommand :=
  genCommand.sound_complete.complete _ (shrinkCommand_ok (genCommand.sound_complete.sound _ hc) h)

/--
**The frame shrinker is not closed.** A frame time of 900 units, which the
generator can produce, shrinks to 899, which it cannot: the generator leaves a
gap between half a tick and nine tenths of one, and shrinking walks into it.
-/
theorem shrinkElapsed_not_closed :
    Spec.ElapsedOK 900 ∧ 899 ∈ shrinkElapsed 900 ∧ ¬ Spec.ElapsedOK 899 := by
  decide

end PropTest
