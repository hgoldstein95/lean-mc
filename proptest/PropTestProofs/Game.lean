import PropTestProofs.Basic

/-!
# The generators of commands, frames and rays are correct
-/

open LeanMc PropTest RandomChoice

namespace PropTest

theorem genCommand.sound_complete : IsSoundAndComplete genCommand Spec.CommandOK := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [genInput.sound_complete.sound.obs, genLook.sound_complete.sound.obs,
      genAction.sound_complete.sound.obs, genSelect.sound_complete.sound.obs]
    exact ⟨‹_›, ‹_›⟩
  case complete =>
    intro c hc
    rw [genCommand, SPMF.mem_support_iff_may]
    walk [genInput.sound_complete.complete.obs, genLook.sound_complete.complete.obs,
      genAction.sound_complete.complete.obs, genSelect.sound_complete.complete.obs]
    exact ⟨c.move, hc.1, c.look, hc.2, c.action, c.select, rfl⟩

theorem genCommand.terminates : IsAlmostSurelyTerminating genCommand := by
  mass_fixpoint [genInput.terminates.obs, genLook.terminates.obs, genAction.terminates.obs,
    genSelect.terminates.obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genCommand.faithful : IsFaithful genCommand := by
  faithful_fixpoint [genCommand.terminates, genInput.faithful, genLook.faithful,
    genAction.faithful, genSelect.faithful]

/-- A command takes at most 14 random choices. -/
theorem genCommand.cost_bounded : IsCostBounded genCommand fun _ => 14 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [genInput.cost_bounded.obs, genLook.cost_bounded.obs, genAction.cost_bounded.obs,
    genSelect.cost_bounded.obs]
  all_goals omega

/-- A run of commands is any list of at most `n` commands the command generator can produce. -/
theorem genCommands.sound_complete (n : Nat) :
    IsSoundAndComplete (genCommands n) fun cs => cs.length ≤ n ∧ ∀ c ∈ cs, Spec.CommandOK c := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [genCommand.sound_complete.sound.obs]
    all_goals simp_all
  case complete =>
    intro cs hcs
    rw [genCommands, SPMF.mem_support_iff_may]
    walk [genCommand.sound_complete.complete.obs]
    exact hcs

theorem genCommands.terminates (n : Nat) : IsAlmostSurelyTerminating (genCommands n) := by
  mass_fixpoint [genCommand.terminates.obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genCommands.faithful (n : Nat) : IsFaithful (genCommands n) := by
  faithful_fixpoint [genCommands.terminates n, genCommand.faithful]

theorem genCommands.cost_bounded (n : Nat) :
    IsCostBounded (genCommands n) fun cs => 1 + 14 * cs.length := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [genCommand.cost_bounded.obs]
  all_goals simp at *
  all_goals omega

theorem genSeededCommands.sound_complete :
    IsSoundAndComplete genSeededCommands Spec.SeededCommandsOK := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [(genCommands.sound_complete 60).sound.obs]
    exact ⟨‹_›, ‹_›⟩
  case complete =>
    intro p hp
    rw [genSeededCommands, SPMF.mem_support_iff_may]
    walk [(genCommands.sound_complete 60).complete.obs]
    exact ⟨p.1, hp.1, p.2, hp.2, rfl⟩

theorem genSeededCommands.terminates : IsAlmostSurelyTerminating genSeededCommands := by
  mass_fixpoint [(genCommands.terminates 60).obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genSeededCommands.faithful : IsFaithful genSeededCommands := by
  faithful_fixpoint [genSeededCommands.terminates, genCommands.faithful 60]

theorem genSeededCommands.cost_bounded :
    IsCostBounded genSeededCommands fun p => 2 + 14 * p.2.length := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [(genCommands.cost_bounded 60).obs]
  all_goals omega

/-! ## Frames -/

theorem genFrame.sound_complete : IsSoundAndComplete genFrame Spec.FrameOK := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [genInput.sound_complete.sound.obs, genLook.sound_complete.sound.obs,
      genSelect.sound_complete.sound.obs, genElapsed.sound_complete.sound.obs]
    exact ⟨‹_›, ‹_›, ‹_›⟩
  case complete =>
    intro f hf
    rw [genFrame, SPMF.mem_support_iff_may]
    walk [genInput.sound_complete.complete.obs, genLook.sound_complete.complete.obs,
      chance.complete_obs 20, genSelect.sound_complete.complete.obs, chance.complete_obs 8,
      genElapsed.sound_complete.complete.obs]
    exact ⟨f.move, hf.1, f.look, hf.2.1, f.dig, f.place, f.select, f.fly, f.elapsed, hf.2.2, rfl⟩

theorem genFrame.terminates : IsAlmostSurelyTerminating genFrame := by
  mass_fixpoint [genInput.terminates.obs, genLook.terminates.obs, genSelect.terminates.obs,
    genElapsed.terminates.obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genFrame.faithful : IsFaithful genFrame := by
  faithful_fixpoint [genFrame.terminates, genInput.faithful, genLook.faithful, genSelect.faithful,
    genElapsed.faithful]

/-- A frame takes at most 18 random choices. -/
theorem genFrame.cost_bounded : IsCostBounded genFrame fun _ => 18 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [genInput.cost_bounded.obs, genLook.cost_bounded.obs, genSelect.cost_bounded.obs,
    genElapsed.cost_bounded.obs]
  all_goals omega

/-- A run of frames is any list of at most 120 frames the frame generator can produce. -/
theorem genFrames.sound_complete :
    IsSoundAndComplete genFrames fun fs => fs.length ≤ 120 ∧ ∀ f ∈ fs, Spec.FrameOK f := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [genFrame.sound_complete.sound.obs]
    all_goals simp_all
  case complete =>
    intro fs hfs
    rw [genFrames, SPMF.mem_support_iff_may]
    walk [genFrame.sound_complete.complete.obs]
    exact hfs

theorem genFrames.terminates : IsAlmostSurelyTerminating genFrames := by
  mass_fixpoint [genFrame.terminates.obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genFrames.faithful : IsFaithful genFrames := by
  faithful_fixpoint [genFrames.terminates, genFrame.faithful]

theorem genFrames.cost_bounded : IsCostBounded genFrames fun fs => 1 + 18 * fs.length := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [genFrame.cost_bounded.obs]
  all_goals simp at *
  all_goals omega

/-! ## Rays -/

theorem genRay.sound_complete : IsSoundAndComplete genRay Spec.RayOK := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [genLook.sound_complete.sound.obs]
    simp_all [Spec.RayOK, Spec.Within]
  case complete =>
    intro r hr
    rw [genRay, SPMF.mem_support_iff_may]
    walk [genLook.sound_complete.complete.obs]
    exact ⟨r.1.x, hr.1, r.1.y, hr.2.1, r.1.z, hr.2.2.1, r.2, hr.2.2.2, rfl⟩

theorem genRay.terminates : IsAlmostSurelyTerminating genRay := by
  mass_fixpoint [genLook.terminates.obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genRay.faithful : IsFaithful genRay := by
  faithful_fixpoint [genRay.terminates, genLook.faithful]

theorem genRay.cost_bounded : IsCostBounded genRay fun _ => 7 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [genLook.cost_bounded.obs]
  all_goals omega

end PropTest
