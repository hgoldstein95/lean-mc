import PropTestProofs.Tactic
import PropTest.Spec

/-!
# The generators of commands and frames are correct

For each generator: it produces exactly the values its predicate in
`PropTest.Spec` allows (`sound_complete`), it always returns (`terminates`),
what `IO` runs has the distribution these proofs are about (`faithful`), and
it makes at most a stated number of random choices (`cost_bounded`).
-/

open LeanMc PropTest RandomChoice

namespace PropTest

/-! ## Coins -/

theorem chance.sound_complete {p : Nat} (h0 : 0 < p) (h1 : p < 100) :
    IsSoundAndComplete (chance p) fun _ => True := by
  refine .intro (fun _ _ => trivial) ?complete
  intro b _
  rw [chance, SPMF.mem_support_iff_may]; walk
  cases b
  · exact ⟨99, by omega, by simp; omega⟩
  · exact ⟨0, by omega, by simp; omega⟩

/-- A coin that is neither always heads nor always tails can come up either way. -/
theorem chance.complete_obs (p : Nat) (h0 : 0 < p := by decide) (h1 : p < 100 := by decide) :
    ∀ b : Bool, True → SPMF.mayObs.spec (chance p) (· = b) :=
  (chance.sound_complete h0 h1).complete.obs

theorem chance.terminates (p : Nat) : IsAlmostSurelyTerminating (chance p) := by
  mass_fixpoint using SPMF.LfpIsOne.one
  mass_arith

theorem chance.faithful (p : Nat) : IsFaithful (chance p) := by
  faithful_fixpoint [chance.terminates p]

theorem chance.cost_bounded (p : Nat) : IsCostBounded (chance p) fun _ => 1 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  all_goals omega

/-! ## Speeds and inputs -/

theorem genSpeed.sound_complete : IsSoundAndComplete genSpeed Spec.Speed := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint
    all_goals first
      | by_elements
      | (simp_all [Spec.Speed, Spec.Within]; done)
      | (simp_all [Spec.Speed, Spec.Within]; omega)
  case complete =>
    intro v hv
    rw [genSpeed, SPMF.mem_support_iff_may]; walk
    exact .inr (.inr (.inr (.inr hv)))

theorem genSpeed.terminates : IsAlmostSurelyTerminating genSpeed := by
  mass_fixpoint using SPMF.LfpIsOne.one
  mass_arith

theorem genSpeed.faithful : IsFaithful genSpeed := by
  faithful_fixpoint [genSpeed.terminates]

theorem genSpeed.cost_bounded : IsCostBounded genSpeed fun _ => 2 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  all_goals omega

theorem genInput.sound_complete : IsSoundAndComplete genInput Spec.InputOK := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [genSpeed.sound_complete.sound.obs]
    exact ⟨‹_›, ‹_›⟩
  case complete =>
    intro i hi
    rw [genInput, SPMF.mem_support_iff_may]
    walk [genSpeed.sound_complete.complete.obs, chance.complete_obs 25, chance.complete_obs 10,
      chance.complete_obs 3]
    exact ⟨i.wishX, hi.1, i.wishZ, hi.2, i.jump, i.descend, i.toggleFly, rfl⟩

theorem genInput.terminates : IsAlmostSurelyTerminating genInput := by
  mass_fixpoint [genSpeed.terminates.obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genInput.faithful : IsFaithful genInput := by
  faithful_fixpoint [genInput.terminates, genSpeed.faithful]

theorem genInput.cost_bounded : IsCostBounded genInput fun _ => 7 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [genSpeed.cost_bounded.obs]
  all_goals omega

/-! ## Looks -/

theorem genLook.sound_complete : IsSoundAndComplete genLook Spec.LookOK := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint
    all_goals first
      | by_elements
      | (simp_all [Spec.LookOK, Spec.Cube, Spec.Within]; done)
      | (simp_all [Spec.LookOK, Spec.Cube, Spec.Within]; omega)
  case complete =>
    intro v hv
    rw [genLook, SPMF.mem_support_iff_may]; walk
    exact .inr (.inr (.inr ⟨v.x, hv.1, v.y, hv.2.1, v.z, hv.2.2, rfl⟩))

theorem genLook.terminates : IsAlmostSurelyTerminating genLook := by
  mass_fixpoint using SPMF.LfpIsOne.one
  mass_arith

theorem genLook.faithful : IsFaithful genLook := by
  faithful_fixpoint [genLook.terminates]

theorem genLook.cost_bounded : IsCostBounded genLook fun _ => 4 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  all_goals omega

/-! ## Blocks, slots and actions -/

theorem genBlock.sound_complete : IsSoundAndComplete genBlock fun _ => True := by
  refine .intro (fun _ _ => trivial) ?complete
  intro b _
  rw [genBlock, SPMF.mem_support_iff_may]; walk
  cases b <;> simp

theorem genBlock.terminates : IsAlmostSurelyTerminating genBlock := by
  mass_fixpoint using SPMF.LfpIsOne.one
  mass_arith

theorem genBlock.faithful : IsFaithful genBlock := by
  faithful_fixpoint [genBlock.terminates]

theorem genBlock.cost_bounded : IsCostBounded genBlock fun _ => 2 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  all_goals omega

theorem genAnyBlock.sound_complete : IsSoundAndComplete genAnyBlock fun _ => True := by
  refine .intro (fun _ _ => trivial) ?complete
  intro b _
  rw [genAnyBlock, SPMF.mem_support_iff_may]; walk
  cases b <;> simp

theorem genAnyBlock.terminates : IsAlmostSurelyTerminating genAnyBlock := by
  mass_fixpoint using SPMF.LfpIsOne.one
  mass_arith

theorem genAnyBlock.faithful : IsFaithful genAnyBlock := by
  faithful_fixpoint [genAnyBlock.terminates]

theorem genAnyBlock.cost_bounded : IsCostBounded genAnyBlock fun _ => 1 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  all_goals omega

theorem genSelect.sound_complete : IsSoundAndComplete genSelect fun _ => True := by
  refine .intro (fun _ _ => trivial) ?complete
  intro s _
  rw [genSelect, SPMF.mem_support_iff_may]
  walk [chance.complete_obs 15]
  cases s with
  | none => exact ⟨false, 0, by omega, by simp⟩
  | some i => exact ⟨true, i.val, by omega, by simp [Nat.mod_eq_of_lt i.isLt]⟩

theorem genSelect.terminates : IsAlmostSurelyTerminating genSelect := by
  mass_fixpoint using SPMF.LfpIsOne.one
  mass_arith

theorem genSelect.faithful : IsFaithful genSelect := by
  faithful_fixpoint [genSelect.terminates]

theorem genSelect.cost_bounded : IsCostBounded genSelect fun _ => 2 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  all_goals omega

theorem genSlot9.sound_complete : IsSoundAndComplete genSlot9 fun _ => True := by
  refine .intro (fun _ _ => trivial) ?complete
  intro i _
  rw [genSlot9, SPMF.mem_support_iff_may]; walk
  exact ⟨i.val, by omega, by simp [Nat.mod_eq_of_lt i.isLt]⟩

theorem genSlot9.terminates : IsAlmostSurelyTerminating genSlot9 := by
  mass_fixpoint using SPMF.LfpIsOne.one
  mass_arith

theorem genSlot9.faithful : IsFaithful genSlot9 := by
  faithful_fixpoint [genSlot9.terminates]

theorem genSlot9.cost_bounded : IsCostBounded genSlot9 fun _ => 1 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  all_goals omega

theorem genAction.sound_complete : IsSoundAndComplete genAction fun _ => True := by
  refine .intro (fun _ _ => trivial) ?complete
  intro a _
  rw [genAction, SPMF.mem_support_iff_may]; walk
  rcases a with _ | _ | _ <;> simp

theorem genAction.terminates : IsAlmostSurelyTerminating genAction := by
  mass_fixpoint using SPMF.LfpIsOne.one
  mass_arith

theorem genAction.faithful : IsFaithful genAction := by
  faithful_fixpoint [genAction.terminates]

theorem genAction.cost_bounded : IsCostBounded genAction fun _ => 1 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  all_goals omega

/-! ## Frame times and wide integers -/

theorem genElapsed.sound_complete : IsSoundAndComplete genElapsed Spec.ElapsedOK := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint
    all_goals first
      | (simp_all [Spec.ElapsedOK]; done)
      | (simp_all [Spec.ElapsedOK]; omega)
  case complete =>
    intro n hn
    rw [genElapsed, SPMF.mem_support_iff_may]; walk
    simp only [Spec.ElapsedOK] at hn
    omega

theorem genElapsed.terminates : IsAlmostSurelyTerminating genElapsed := by
  mass_fixpoint using SPMF.LfpIsOne.one
  mass_arith

theorem genElapsed.faithful : IsFaithful genElapsed := by
  faithful_fixpoint [genElapsed.terminates]

theorem genElapsed.cost_bounded : IsCostBounded genElapsed fun _ => 2 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  all_goals omega

theorem genWideInt.sound_complete : IsSoundAndComplete genWideInt Spec.Wide := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint
    all_goals first
      | by_elements
      | (simp_all [Spec.Wide, Spec.Within]; done)
      | (simp_all [Spec.Wide, Spec.Within]; omega)
  case complete =>
    intro n hn
    rw [genWideInt, SPMF.mem_support_iff_may]; walk
    rcases hn with hn | hn
    · exact .inr (.inl hn)
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
      refine .inr (.inr ?_)
      simp only [List.mem_cons, List.mem_nil_iff, or_false]
      omega

theorem genWideInt.terminates : IsAlmostSurelyTerminating genWideInt := by
  mass_fixpoint using SPMF.LfpIsOne.one
  mass_arith

theorem genWideInt.faithful : IsFaithful genWideInt := by
  faithful_fixpoint [genWideInt.terminates]

theorem genWideInt.cost_bounded : IsCostBounded genWideInt fun _ => 2 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  all_goals omega

end PropTest
