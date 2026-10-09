import PropTestProofs.Basic

/-!
# The generators of commands to the shim are correct
-/

open LeanMc PropTest RandomChoice

namespace PropTest

theorem genByte.sound_complete : IsSoundAndComplete genByte fun _ => True := by
  refine .intro (fun _ _ => trivial) ?complete
  intro b _
  rw [genByte, SPMF.mem_support_iff_may]
  walk [chance.complete_obs 15]
  refine ⟨true, ?_⟩
  simp only [↓reduceIte]
  exact ⟨b.toNat, ⟨Nat.zero_le _, by have := b.toNat_lt; omega⟩, by simp⟩

theorem genByte.terminates : IsAlmostSurelyTerminating genByte := by
  mass_fixpoint using SPMF.LfpIsOne.one
  mass_arith

theorem genByte.faithful : IsFaithful genByte := by
  faithful_fixpoint [genByte.terminates]

theorem genByte.cost_bounded : IsCostBounded genByte fun _ => 2 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  all_goals omega

/-- `genBytes n` produces exactly the byte arrays of size `n`. -/
theorem genBytes.sound_complete (n : Nat) :
    IsSoundAndComplete (genBytes n) fun v => v.size = n := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [genByte.sound_complete.sound.obs]
    rename_i xs hxs
    simpa [ByteArray.size] using hxs.1
  case complete =>
    intro v hv
    obtain ⟨data⟩ := v
    rw [genBytes, SPMF.mem_support_iff_may]
    walk [genByte.sound_complete.complete.obs]
    exact ⟨data.toList, ⟨hv, fun _ _ => trivial⟩, rfl⟩

theorem genBytes.terminates (n : Nat) : IsAlmostSurelyTerminating (genBytes n) := by
  mass_fixpoint [genByte.terminates.obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genBytes.faithful (n : Nat) : IsFaithful (genBytes n) := by
  faithful_fixpoint [genBytes.terminates n, genByte.faithful]

/-- Two random choices a byte. -/
theorem genBytes.cost_bounded (n : Nat) : IsCostBounded (genBytes n) fun v => 2 * v.size := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [genByte.cost_bounded.obs]
  all_goals simp [ByteArray.size] at *
  all_goals omega

theorem ByteArray.empty_eq_of_size_eq_zero {v : ByteArray} (h : v.size = 0) :
    ByteArray.empty = v := by
  obtain ⟨data⟩ := v
  have : data = #[] := Array.eq_empty_of_size_eq_zero h
  subst this
  rfl

theorem genMesh.sound_complete : IsSoundAndComplete genMesh fun v => Spec.MeshSizeOK v.size := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [fun n => (genBytes.sound_complete n).sound.obs]
    all_goals first
      | decide
      | (simp_all [Spec.MeshSizeOK]; done)
      | (simp_all [Spec.MeshSizeOK]; omega)
  case complete =>
    intro v hv
    rw [genMesh, SPMF.mem_support_iff_may]
    walk [fun n => (genBytes.sound_complete n).complete.obs]
    simp only [Spec.MeshSizeOK, List.mem_cons, List.mem_nil_iff, or_false] at hv
    by_cases h24 : v.size % 24 = 0 ∧ v.size ≠ 0
    · exact .inl ⟨v.size / 24, by omega, by omega⟩
    · by_cases h0 : v.size = 0
      · exact .inr (.inl (ByteArray.empty_eq_of_size_eq_zero h0))
      · refine .inr (.inr ⟨v.size, ?_, rfl⟩)
        simp only [List.mem_cons, List.mem_nil_iff, or_false]
        omega

theorem genMesh.terminates : IsAlmostSurelyTerminating genMesh := by
  mass_fixpoint [fun n => (genBytes.terminates n).obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genMesh.faithful : IsFaithful genMesh := by
  faithful_fixpoint [genMesh.terminates, genBytes.faithful]

theorem genMesh.cost_bounded : IsCostBounded genMesh fun v => 2 + 2 * v.size := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [fun n => (genBytes.cost_bounded n).obs]
  all_goals omega

theorem genSlot.sound_complete : IsSoundAndComplete genSlot Spec.SlotOK := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint
    all_goals first
      | by_elements
      | simp_all [Spec.SlotOK]
  case complete =>
    intro n hn
    rw [genSlot, SPMF.mem_support_iff_may]; walk
    simp only [Spec.SlotOK, List.mem_cons, List.mem_nil_iff, or_false] at hn ⊢
    omega

theorem genSlot.terminates : IsAlmostSurelyTerminating genSlot := by
  mass_fixpoint using SPMF.LfpIsOne.one
  mass_arith

theorem genSlot.faithful : IsFaithful genSlot := by
  faithful_fixpoint [genSlot.terminates]

theorem genSlot.cost_bounded : IsCostBounded genSlot fun _ => 2 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  all_goals omega

/-! ## Commands -/

theorem genGpuCmd.sound_complete : IsSoundAndComplete genGpuCmd Spec.GpuCmdOK := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [genSlot.sound_complete.sound.obs, genMesh.sound_complete.sound.obs]
    all_goals simp_all [Spec.GpuCmdOK, Spec.Cube, Spec.Within]
  case complete =>
    intro cmd hcmd
    cases cmd with
    | upload slot vertices =>
      rw [genGpuCmd, SPMF.mem_support_iff_may]
      walk [genSlot.sound_complete.complete.obs, genMesh.sound_complete.complete.obs]
      exact ⟨slot, hcmd.1, vertices, hcmd.2, rfl⟩
    | unload slot =>
      rw [genGpuCmd, SPMF.mem_support_iff_may]
      walk [genSlot.sound_complete.complete.obs, genMesh.sound_complete.complete.obs]
      exact ⟨slot, hcmd, rfl⟩
    | beginScene =>
      rw [genGpuCmd, SPMF.mem_support_iff_may]
      walk [genSlot.sound_complete.complete.obs, genMesh.sound_complete.complete.obs]
    | draw slot offset =>
      rw [genGpuCmd, SPMF.mem_support_iff_may]
      walk [genSlot.sound_complete.complete.obs, genMesh.sound_complete.complete.obs]
      exact ⟨slot, hcmd.1, offset.x, hcmd.2.1, offset.y, hcmd.2.2.1, offset.z, hcmd.2.2.2, rfl⟩

theorem genGpuCmd.terminates : IsAlmostSurelyTerminating genGpuCmd := by
  mass_fixpoint [genSlot.terminates.obs, genMesh.terminates.obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genGpuCmd.faithful : IsFaithful genGpuCmd := by
  faithful_fixpoint [genGpuCmd.terminates, genSlot.faithful, genMesh.faithful]

/-- The most random choices a shim command takes: its mesh's bytes, and a few more. -/
def gpuCmdCost : GpuCmd → Nat
  | .upload _ vertices => 5 + 2 * vertices.size
  | _ => 6

theorem genGpuCmd.cost_bounded : IsCostBounded genGpuCmd gpuCmdCost := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [genSlot.cost_bounded.obs, genMesh.cost_bounded.obs]
  all_goals simp only [gpuCmdCost]
  all_goals omega

/-- A run of shim commands is any list of at most 40 commands the generator can produce. -/
theorem genGpuCmds.sound_complete :
    IsSoundAndComplete genGpuCmds fun cmds => cmds.length ≤ 40 ∧ ∀ cmd ∈ cmds, Spec.GpuCmdOK cmd := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [genGpuCmd.sound_complete.sound.obs]
    all_goals simp_all
  case complete =>
    intro cmds hcmds
    rw [genGpuCmds, SPMF.mem_support_iff_may]
    walk [genGpuCmd.sound_complete.complete.obs]
    exact hcmds

theorem genGpuCmds.terminates : IsAlmostSurelyTerminating genGpuCmds := by
  mass_fixpoint [genGpuCmd.terminates.obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genGpuCmds.faithful : IsFaithful genGpuCmds := by
  faithful_fixpoint [genGpuCmds.terminates, genGpuCmd.faithful]

theorem genGpuCmds.cost_bounded :
    IsCostBounded genGpuCmds fun cmds => 1 + (cmds.map gpuCmdCost).sum := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [genGpuCmd.cost_bounded.obs]
  all_goals omega

/-- The bytes handed to the shim's decoder are any byte array of at most 200 bytes. -/
theorem genDecodeBytes.sound_complete :
    IsSoundAndComplete genDecodeBytes fun v => v.size ≤ 200 := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [fun n => (genBytes.sound_complete n).sound.obs]
    all_goals omega
  case complete =>
    intro v hv
    rw [genDecodeBytes, SPMF.mem_support_iff_may]
    walk [fun n => (genBytes.sound_complete n).complete.obs]
    exact ⟨v.size, ⟨Nat.zero_le _, hv⟩, rfl⟩

theorem genDecodeBytes.terminates : IsAlmostSurelyTerminating genDecodeBytes := by
  mass_fixpoint [fun n => (genBytes.terminates n).obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genDecodeBytes.faithful : IsFaithful genDecodeBytes := by
  faithful_fixpoint [genDecodeBytes.terminates, genBytes.faithful]

theorem genDecodeBytes.cost_bounded : IsCostBounded genDecodeBytes fun v => 1 + 2 * v.size := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [fun n => (genBytes.cost_bounded n).obs]
  all_goals omega

end PropTest
