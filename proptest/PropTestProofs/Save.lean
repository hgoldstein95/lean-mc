import PropTestProofs.Basic

/-!
# The generators of saved games are correct
-/

open LeanMc PropTest RandomChoice

namespace PropTest

/-! ## Inventories -/

theorem genStackSlot.sound_complete : IsSoundAndComplete genStackSlot fun _ => True := by
  refine .intro (fun _ _ => trivial) ?complete
  intro s _
  rw [genStackSlot, SPMF.mem_support_iff_may]
  walk [chance.complete_obs 50, genAnyBlock.sound_complete.complete.obs]
  cases s with
  | none => exact ⟨false, by simp⟩
  | some st =>
    obtain ⟨block, ⟨extra, hextra⟩⟩ := st
    refine ⟨true, ?_⟩
    simp only [↓reduceIte]
    exact ⟨extra, ⟨Nat.zero_le _, by omega⟩, block, by simp [Nat.mod_eq_of_lt hextra]⟩

theorem genStackSlot.terminates : IsAlmostSurelyTerminating genStackSlot := by
  mass_fixpoint [genAnyBlock.terminates.obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genStackSlot.faithful : IsFaithful genStackSlot := by
  faithful_fixpoint [genStackSlot.terminates, genAnyBlock.faithful]

theorem genStackSlot.cost_bounded : IsCostBounded genStackSlot fun _ => 3 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [genAnyBlock.cost_bounded.obs]
  all_goals omega

theorem genInventory.sound_complete : IsSoundAndComplete genInventory fun _ => True := by
  refine .intro (fun _ _ => trivial) ?complete
  intro inv _
  rw [genInventory, SPMF.mem_support_iff_may]
  walk [genStackSlot.sound_complete.complete.obs]
  obtain ⟨slots⟩ := inv
  refine ⟨slots[0], slots[1], slots[2], slots[3], slots[4], slots[5], slots[6], slots[7],
    slots[8], ?_⟩
  congr 1
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

theorem genInventory.terminates : IsAlmostSurelyTerminating genInventory := by
  mass_fixpoint [genStackSlot.terminates.obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genInventory.faithful : IsFaithful genInventory := by
  faithful_fixpoint [genInventory.terminates, genStackSlot.faithful]

theorem genInventory.cost_bounded : IsCostBounded genInventory fun _ => 27 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [genStackSlot.cost_bounded.obs]
  all_goals omega

/-! ## Positions, seeds, edits and players -/

theorem genWideVec.sound_complete : IsSoundAndComplete genWideVec Spec.WideVec := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [genWideInt.sound_complete.sound.obs]
    exact ⟨‹_›, ‹_›, ‹_›⟩
  case complete =>
    intro v hv
    rw [genWideVec, SPMF.mem_support_iff_may]
    walk [genWideInt.sound_complete.complete.obs]
    exact ⟨v.x, hv.1, v.y, hv.2.1, v.z, hv.2.2, rfl⟩

theorem genWideVec.terminates : IsAlmostSurelyTerminating genWideVec := by
  mass_fixpoint [genWideInt.terminates.obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genWideVec.faithful : IsFaithful genWideVec := by
  faithful_fixpoint [genWideVec.terminates, genWideInt.faithful]

theorem genWideVec.cost_bounded : IsCostBounded genWideVec fun _ => 6 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [genWideInt.cost_bounded.obs]
  all_goals omega

theorem genSeed.sound_complete : IsSoundAndComplete genSeed Spec.SeedOK := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint
    all_goals first
      | by_elements
      | (simp [Spec.SeedOK]; omega)
  case complete =>
    intro s hs
    rw [genSeed, SPMF.mem_support_iff_may]; walk
    rcases hs with hs | hs
    · exact .inl ⟨s.toNat, ⟨Nat.zero_le _, hs⟩, by simp⟩
    · exact .inr ⟨s.toNat, hs, by simp⟩

theorem genSeed.terminates : IsAlmostSurelyTerminating genSeed := by
  mass_fixpoint using SPMF.LfpIsOne.one
  mass_arith

theorem genSeed.faithful : IsFaithful genSeed := by
  faithful_fixpoint [genSeed.terminates]

theorem genSeed.cost_bounded : IsCostBounded genSeed fun _ => 2 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  all_goals omega

theorem genEdit.sound_complete : IsSoundAndComplete genEdit Spec.EditOK := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [genWideInt.sound_complete.sound.obs, genAnyBlock.sound_complete.sound.obs]
    exact ⟨‹_›, ‹_›, ‹_›⟩
  case complete =>
    intro e he
    rw [genEdit, SPMF.mem_support_iff_may]
    walk [genWideInt.sound_complete.complete.obs, genAnyBlock.sound_complete.complete.obs]
    exact ⟨e.1.x, he.1, e.1.y, he.2.1, e.1.z, he.2.2, e.2, rfl⟩

theorem genEdit.terminates : IsAlmostSurelyTerminating genEdit := by
  mass_fixpoint [genWideInt.terminates.obs, genAnyBlock.terminates.obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genEdit.faithful : IsFaithful genEdit := by
  faithful_fixpoint [genEdit.terminates, genWideInt.faithful, genAnyBlock.faithful]

theorem genEdit.cost_bounded : IsCostBounded genEdit fun _ => 7 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [genWideInt.cost_bounded.obs, genAnyBlock.cost_bounded.obs]
  all_goals omega

theorem genPlayer.sound_complete : IsSoundAndComplete genPlayer Spec.PlayerOK := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [genWideVec.sound_complete.sound.obs]
    exact ⟨‹_›, ‹_›⟩
  case complete =>
    intro p hp
    rw [genPlayer, SPMF.mem_support_iff_may]
    walk [genWideVec.sound_complete.complete.obs, chance.complete_obs 50]
    exact ⟨p.pos, hp.1, p.vel, hp.2, p.onGround, p.flying, rfl⟩

theorem genPlayer.terminates : IsAlmostSurelyTerminating genPlayer := by
  mass_fixpoint [genWideVec.terminates.obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genPlayer.faithful : IsFaithful genPlayer := by
  faithful_fixpoint [genPlayer.terminates, genWideVec.faithful]

theorem genPlayer.cost_bounded : IsCostBounded genPlayer fun _ => 14 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [genWideVec.cost_bounded.obs]
  all_goals omega

/-! ## Saved games -/

theorem genSaveData.sound_complete : IsSoundAndComplete genSaveData Spec.SaveOK := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [genSeed.sound_complete.sound.obs, genEdit.sound_complete.sound.obs,
      genPlayer.sound_complete.sound.obs, genInventory.sound_complete.sound.obs,
      genSlot9.sound_complete.sound.obs]
    simp_all [Spec.SaveOK]
  case complete =>
    intro d hd
    rw [genSaveData, SPMF.mem_support_iff_may]
    walk [genSeed.sound_complete.complete.obs, genEdit.sound_complete.complete.obs,
      genPlayer.sound_complete.complete.obs, genInventory.sound_complete.complete.obs,
      genSlot9.sound_complete.complete.obs]
    exact ⟨d.seed, hd.1, d.edits, ⟨hd.2.2.1, hd.2.2.2⟩, d.player, hd.2.1, d.inventory,
      d.selected, rfl⟩

theorem genSaveData.terminates : IsAlmostSurelyTerminating genSaveData := by
  mass_fixpoint [genSeed.terminates.obs, genEdit.terminates.obs, genPlayer.terminates.obs,
    genInventory.terminates.obs, genSlot9.terminates.obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genSaveData.faithful : IsFaithful genSaveData := by
  faithful_fixpoint [genSaveData.terminates, genSeed.faithful, genEdit.faithful,
    genPlayer.faithful, genInventory.faithful, genSlot9.faithful]

/-- A saved game takes at most 45 random choices, and 7 more for each edit. -/
theorem genSaveData.cost_bounded :
    IsCostBounded genSaveData fun d => 45 + 7 * d.edits.length := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [genSeed.cost_bounded.obs, genEdit.cost_bounded.obs, genPlayer.cost_bounded.obs,
    genInventory.cost_bounded.obs, genSlot9.cost_bounded.obs]
  all_goals simp at *
  all_goals omega

/-! ## Saves with one integer changed -/

theorem length_flatMap_encodeSlot (l : List (Option Stack)) :
    (l.flatMap SaveData.encodeSlot).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    cases s <;> simp only [List.flatMap_cons, List.length_append, SaveData.encodeSlot,
      List.length_cons, List.length_nil, ih] <;> omega

theorem length_flatMap_encodeEdit (l : List (BlockPos × Block)) :
    (l.flatMap SaveData.encodeEdit).length = 4 * l.length := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [List.flatMap_cons, List.length_append, SaveData.encodeEdit, List.length_cons,
      List.length_nil, ih]
    omega

/-- A saved game is 31 integers and four more for each edit. -/
theorem length_encode (d : SaveData) : d.encode.length = 31 + 4 * d.edits.length := by
  simp only [SaveData.encode, List.length_append, List.length_cons, List.length_nil,
    length_flatMap_encodeSlot, length_flatMap_encodeEdit, Vector.length_toList]
  omega

theorem genMutatedSave.sound_complete : IsSoundAndComplete genMutatedSave Spec.MutatedSaveOK := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [genSaveData.sound_complete.sound.obs, genWideInt.sound_complete.sound.obs]
    rename_i d hd i hi w hw
    exact ⟨d, hd, i % d.encode.length, Nat.mod_lt _ (by rw [length_encode]; omega), w, hw, rfl⟩
  case complete =>
    intro ints hints
    obtain ⟨d, hd, j, hj, w, hw, rfl⟩ := hints
    rw [genMutatedSave, SPMF.mem_support_iff_may]
    walk [genSaveData.sound_complete.complete.obs, genWideInt.sound_complete.complete.obs]
    have hlen := length_encode d
    have hedits := hd.2.2.1
    exact ⟨d, hd, j, ⟨Nat.zero_le _, by omega⟩, w, hw, by rw [Nat.mod_eq_of_lt hj]⟩

theorem genMutatedSave.terminates : IsAlmostSurelyTerminating genMutatedSave := by
  mass_fixpoint [genSaveData.terminates.obs, genWideInt.terminates.obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genMutatedSave.faithful : IsFaithful genMutatedSave := by
  faithful_fixpoint [genMutatedSave.terminates, genSaveData.faithful, genWideInt.faithful]

/-- A mutated save takes at most 48 random choices and two more for each integer in it. -/
theorem genMutatedSave.cost_bounded :
    IsCostBounded genMutatedSave fun ints => 48 + 2 * ints.length := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [genSaveData.cost_bounded.obs, genWideInt.cost_bounded.obs]
  all_goals simp only [List.length_set, length_encode] at *
  all_goals omega

end PropTest
