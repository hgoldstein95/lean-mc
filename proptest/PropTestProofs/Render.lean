import PropTestProofs.Basic

/-!
# The generators of renderer operations are correct
-/

open LeanMc PropTest RandomChoice

namespace PropTest

theorem genChunk.sound_complete : IsSoundAndComplete genChunk Spec.ChunkOK := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint
    simp_all [Spec.ChunkOK, Spec.Within]
  case complete =>
    intro c hc
    rw [genChunk, SPMF.mem_support_iff_may]; walk
    exact ⟨c.x, hc.1, c.y, hc.2.1, c.z, hc.2.2, rfl⟩

theorem genChunk.terminates : IsAlmostSurelyTerminating genChunk := by
  mass_fixpoint using SPMF.LfpIsOne.one
  mass_arith

theorem genChunk.faithful : IsFaithful genChunk := by
  faithful_fixpoint [genChunk.terminates]

theorem genChunk.cost_bounded : IsCostBounded genChunk fun _ => 3 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  all_goals omega

theorem genCentre.sound_complete : IsSoundAndComplete genCentre Spec.CentreOK := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint
    simp_all [Spec.CentreOK, Spec.Within]
  case complete =>
    intro c hc
    rw [genCentre, SPMF.mem_support_iff_may]; walk
    exact ⟨c.x, hc.1, c.y, hc.2.1, c.z, hc.2.2, rfl⟩

theorem genCentre.terminates : IsAlmostSurelyTerminating genCentre := by
  mass_fixpoint using SPMF.LfpIsOne.one
  mass_arith

theorem genCentre.faithful : IsFaithful genCentre := by
  faithful_fixpoint [genCentre.terminates]

theorem genCentre.cost_bounded : IsCostBounded genCentre fun _ => 3 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  all_goals omega

theorem genEditY.sound_complete : IsSoundAndComplete genEditY Spec.EditYOK := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint
    all_goals first
      | by_elements
      | (simp_all [Spec.EditYOK, Spec.Within]; done)
      | (simp_all [Spec.EditYOK, Spec.Within]; omega)
  case complete =>
    intro y hy
    rw [genEditY, SPMF.mem_support_iff_may]; walk
    simp only [Spec.EditYOK, Spec.Within] at hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    omega

theorem genEditY.terminates : IsAlmostSurelyTerminating genEditY := by
  mass_fixpoint using SPMF.LfpIsOne.one
  mass_arith

theorem genEditY.faithful : IsFaithful genEditY := by
  faithful_fixpoint [genEditY.terminates]

theorem genEditY.cost_bounded : IsCostBounded genEditY fun _ => 2 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint
  all_goals omega

theorem genEditCoord.sound_complete (edge : Bool) :
    IsSoundAndComplete (genEditCoord edge) (Spec.EditCoordOK edge) := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    cases edge <;> walk fixpoint <;> simp_all [Spec.EditCoordOK, Spec.Within]
  case complete =>
    intro v hv
    cases edge <;> (rw [genEditCoord, SPMF.mem_support_iff_may]; walk) <;>
      simpa [Spec.EditCoordOK, Spec.Within] using hv

theorem genEditCoord.terminates (edge : Bool) : IsAlmostSurelyTerminating (genEditCoord edge) := by
  cases edge <;> (mass_fixpoint using SPMF.LfpIsOne.one) <;> mass_arith

theorem genEditCoord.faithful (edge : Bool) : IsFaithful (genEditCoord edge) := by
  faithful_fixpoint [genEditCoord.terminates edge]

theorem genEditCoord.cost_bounded (edge : Bool) : IsCostBounded (genEditCoord edge) fun _ => 1 := by
  rw [IsCostBounded.iff_obs]
  cases edge <;> walk fixpoint <;> omega

theorem genEditPos.sound_complete : IsSoundAndComplete genEditPos Spec.EditPosOK := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [fun e => (genEditCoord.sound_complete e).sound.obs,
      genEditY.sound_complete.sound.obs]
    generalize decide (_ < 40) = edge at *
    cases edge <;> first
      | (simp_all [Spec.EditCoordOK, Spec.EditPosOK, Spec.Within]; done)
      | (simp_all [Spec.EditCoordOK, Spec.EditPosOK, Spec.Within]; omega)
  case complete =>
    intro p hp
    rw [genEditPos, SPMF.mem_support_iff_may]
    walk [chance.complete_obs 40, fun e => (genEditCoord.sound_complete e).complete.obs,
      genEditY.sound_complete.complete.obs]
    exact ⟨false, p.x, by simpa [Spec.EditCoordOK] using hp.1, p.y, hp.2.1, p.z,
      by simpa [Spec.EditCoordOK] using hp.2.2, rfl⟩

theorem genEditPos.terminates : IsAlmostSurelyTerminating genEditPos := by
  mass_fixpoint [fun e => (genEditCoord.terminates e).obs, genEditY.terminates.obs]
    using SPMF.LfpIsOne.one
  mass_arith

theorem genEditPos.faithful : IsFaithful genEditPos := by
  faithful_fixpoint [genEditPos.terminates, genEditCoord.faithful, genEditY.faithful]

theorem genEditPos.cost_bounded : IsCostBounded genEditPos fun _ => 5 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [fun e => (genEditCoord.cost_bounded e).obs, genEditY.cost_bounded.obs]
  all_goals omega

/-! ## Operations -/

theorem genRenderOp.sound_complete : IsSoundAndComplete genRenderOp Spec.RenderOpOK := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [genChunk.sound_complete.sound.obs, genEditPos.sound_complete.sound.obs,
      genBlock.sound_complete.sound.obs, genCentre.sound_complete.sound.obs]
    all_goals simp_all [Spec.RenderOpOK, Spec.Within]
  case complete =>
    intro op hop
    cases op with
    | mesh c =>
      rw [genRenderOp, SPMF.mem_support_iff_may]
      walk [genChunk.sound_complete.complete.obs, genEditPos.sound_complete.complete.obs,
        genBlock.sound_complete.complete.obs, genCentre.sound_complete.complete.obs]
      exact ⟨c, hop, rfl⟩
    | edit p b =>
      rw [genRenderOp, SPMF.mem_support_iff_may]
      walk [genChunk.sound_complete.complete.obs, genEditPos.sound_complete.complete.obs,
        genBlock.sound_complete.complete.obs, genCentre.sound_complete.complete.obs]
      exact ⟨p, hop, b, rfl⟩
    | dropFar c =>
      rw [genRenderOp, SPMF.mem_support_iff_may]
      walk [genChunk.sound_complete.complete.obs, genEditPos.sound_complete.complete.obs,
        genBlock.sound_complete.complete.obs, genCentre.sound_complete.complete.obs]
      exact ⟨c, hop, rfl⟩
    | draw e =>
      rw [genRenderOp, SPMF.mem_support_iff_may]
      walk [genChunk.sound_complete.complete.obs, genEditPos.sound_complete.complete.obs,
        genBlock.sound_complete.complete.obs, genCentre.sound_complete.complete.obs]
      exact ⟨e.x, hop.1, e.y, hop.2.1, e.z, hop.2.2, rfl⟩

theorem genRenderOp.terminates : IsAlmostSurelyTerminating genRenderOp := by
  mass_fixpoint [genChunk.terminates.obs, genEditPos.terminates.obs, genBlock.terminates.obs,
    genCentre.terminates.obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genRenderOp.faithful : IsFaithful genRenderOp := by
  faithful_fixpoint [genRenderOp.terminates, genChunk.faithful, genEditPos.faithful,
    genBlock.faithful, genCentre.faithful]

/-- A renderer operation takes at most 8 random choices. -/
theorem genRenderOp.cost_bounded : IsCostBounded genRenderOp fun _ => 8 := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [genChunk.cost_bounded.obs, genEditPos.cost_bounded.obs,
    genBlock.cost_bounded.obs, genCentre.cost_bounded.obs]
  all_goals omega

/-- A run of operations is any list of at most 30 operations the generator can produce. -/
theorem genRenderOps.sound_complete :
    IsSoundAndComplete genRenderOps fun ops => ops.length ≤ 30 ∧ ∀ op ∈ ops, Spec.RenderOpOK op := by
  refine .intro ?sound ?complete
  case sound =>
    rw [IsSoundFor.iff_obs]
    walk fixpoint [genRenderOp.sound_complete.sound.obs]
    all_goals simp_all
  case complete =>
    intro ops hops
    rw [genRenderOps, SPMF.mem_support_iff_may]
    walk [genRenderOp.sound_complete.complete.obs]
    exact hops

theorem genRenderOps.terminates : IsAlmostSurelyTerminating genRenderOps := by
  mass_fixpoint [genRenderOp.terminates.obs] using SPMF.LfpIsOne.one
  mass_arith

theorem genRenderOps.faithful : IsFaithful genRenderOps := by
  faithful_fixpoint [genRenderOps.terminates, genRenderOp.faithful]

theorem genRenderOps.cost_bounded : IsCostBounded genRenderOps fun ops => 1 + 8 * ops.length := by
  rw [IsCostBounded.iff_obs]
  walk fixpoint [genRenderOp.cost_bounded.obs]
  all_goals simp at *
  all_goals omega

end PropTest
