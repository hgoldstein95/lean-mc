import PropTestProofs.Game
import PropTestProofs.Render
import PropTestProofs.Gpu
import PropTestProofs.Save
import LeanMc.Proofs.View
import LeanMc.Proofs.Save

/-!
# The generators reach the cases the theorems are about

That a generator produces exactly its predicate's values says nothing about
whether those values exercise anything. Each theorem here names a case that a
proof in `LeanMc.Proofs` has to treat separately and shows the generator for
the matching property can produce it. They are consequences of completeness:
exhibit a value in the predicate and check it has the case.

A case can be reachable and still vanishingly rare, which these cannot see; the
`refutes` self-checks in `Props.lean` are what show a case is actually found.
-/

open LeanMc PropTest RandomChoice

namespace PropTest

/-! ## Pacing -/

/--
**Every number of ticks, with every combination of presses.** Whatever time a
session is owed, the frame generator can produce a frame that runs any number
of ticks up to the per-frame limit, carrying any presses. With one tick and
both a dig and a place, this is the case where the place waits for the next
tick; with none, the case where everything waits.
-/
theorem genFrame_covers_ticks (s : Session) (hs : s.debt < unitsPerTick) {k : Nat}
    (hk : k ≤ maxTicksPerFrame) (dig place fly : Bool) (select : Option (Fin 9)) :
    ∃ f ∈ SPMF.support genFrame, s.ticksDue f = k ∧ f.dig = dig ∧ f.place = place
      ∧ f.fly = fly ∧ f.select = select := by
  refine ⟨{ dig, place, fly, select, elapsed := k * 1000 },
    genFrame.sound_complete.complete _
      ⟨(by decide : Spec.InputOK {}), (by decide : Spec.LookOK ⟨0, 0, 0⟩), ?_⟩,
    ?_, rfl, rfl, rfl, rfl⟩
  · simp only [Spec.ElapsedOK, maxTicksPerFrame] at hk ⊢
    omega
  · simp only [Session.ticksDue, Session.ticksOwed, unitsPerTick, maxTicksPerFrame] at hs hk ⊢
    omega

/-- **A stalled frame**, owing more ticks than one frame may run, so that time is dropped. -/
theorem genFrame_covers_stall (s : Session) :
    ∃ f ∈ SPMF.support genFrame, maxTicksPerFrame < s.ticksOwed f := by
  refine ⟨{ elapsed := 200000 }, genFrame.sound_complete.complete _ ⟨by decide, by decide, ?_⟩, ?_⟩
  · simp [Spec.ElapsedOK]
  · simp only [Session.ticksOwed, unitsPerTick, maxTicksPerFrame]
    omega

/-! ## Commands -/

/-- **Every action with every slot choice**: nothing, a dig or a place, whatever slot key is down. -/
theorem genCommand_covers_actions (action : Option Action) (select : Option (Fin 9)) :
    ∃ c ∈ SPMF.support genCommand, c.action = action ∧ c.select = select :=
  ⟨{ action, select }, genCommand.sound_complete.complete _
    ⟨(by decide : Spec.InputOK {}), (by decide : Spec.LookOK ⟨0, 0, 0⟩)⟩, rfl, rfl⟩

/--
**Looks on both sides of the reach**: the zero vector, a look the reach leaves
alone, and a look too long for it, which is scaled down.
-/
theorem genLook_covers_reach :
    (⟨0, 0, 0⟩ : Vec3) ∈ SPMF.support genLook
      ∧ (∃ v ∈ SPMF.support genLook, v ≠ ⟨0, 0, 0⟩ ∧ State.reachVector v = v)
      ∧ (∃ v ∈ SPMF.support genLook, State.reachVector v ≠ v) :=
  ⟨genLook.sound_complete.complete _ (by decide),
    ⟨⟨327680, -327680, 0⟩, genLook.sound_complete.complete _ (by decide), by decide, by decide⟩,
    ⟨⟨3276800, 327680, 0⟩, genLook.sound_complete.complete _ (by decide), by decide⟩⟩

/-! ## The renderer -/

/-- **An edit on a horizontal chunk corner**, whose change touches three chunks' meshes. -/
theorem genRenderOp_covers_corner :
    ∃ p b, RenderOp.edit p b ∈ SPMF.support genRenderOp ∧ (dirtyChunks p).length = 3 :=
  ⟨⟨0, 1, 0⟩, .stone, genRenderOp.sound_complete.complete _ (by decide), by decide⟩

/-- **An edit on a vertical chunk boundary**, which touches the mesh of the chunk above or below. -/
theorem genRenderOp_covers_vertical :
    ∃ p b, RenderOp.edit p b ∈ SPMF.support genRenderOp
      ∧ ∃ c ∈ dirtyChunks p, c.y ≠ p.chunkPos.y :=
  ⟨⟨5, 15, 5⟩, .stone, genRenderOp.sound_complete.complete _ (by decide),
    ((⟨5, 15, 5⟩ : BlockPos).step .yp).chunkPos, mem_dirtyChunks.mpr (.inr ⟨.yp, rfl⟩),
    by decide⟩

/--
**A view centre far from any meshed chunk.** Whichever chunk has been meshed,
some centre the generator can produce puts it out of view, so that it is
dropped, its slot emptied and later reused.
-/
theorem genRenderOp_covers_far (c : ChunkPos) (hc : Spec.ChunkOK c) :
    ∃ centre, RenderOp.dropFar centre ∈ SPMF.support genRenderOp
      ∧ (⟨1, 1⟩ : ViewRange).isFar centre c 1 = true := by
  refine ⟨⟨4, 0, 0⟩, genRenderOp.sound_complete.complete _ (by decide), ?_⟩
  obtain ⟨⟨h1, h2⟩, -, -⟩ := hc
  simp only [ViewRange.isFar, ViewRange.contains, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not]
  omega

/-! ## The shim -/

/-- **Every kind of slot**: zero, ordinary, the last valid one, the first invalid one, and one past 32 bits. -/
theorem genSlot_covers :
    ∀ n ∈ [0, 3, 16383, 16384, 4294967299], n ∈ SPMF.support genSlot := by
  intro n hn
  refine genSlot.sound_complete.complete _ ?_
  revert n
  decide

/--
**Every misuse the model calls a fault**: an upload to slot zero, to a slot
past the table, of an empty mesh, and of a mesh that is not whole triangles;
and an unload and a draw of slots that hold nothing.
-/
theorem genGpuCmd_covers_misuse :
    (∃ v, GpuCmd.upload 0 v ∈ SPMF.support genGpuCmd)
      ∧ (∃ v, GpuCmd.upload Gpu.capacity v ∈ SPMF.support genGpuCmd)
      ∧ GpuCmd.upload 1 ByteArray.empty ∈ SPMF.support genGpuCmd
      ∧ (∃ v, v.size % Gpu.triangleBytes ≠ 0 ∧ GpuCmd.upload 1 v ∈ SPMF.support genGpuCmd)
      ∧ GpuCmd.unload 0 ∈ SPMF.support genGpuCmd
      ∧ (∃ o, GpuCmd.draw 4294967299 o ∈ SPMF.support genGpuCmd) :=
  ⟨⟨ByteArray.empty, genGpuCmd.sound_complete.complete _ (by decide)⟩,
    ⟨ByteArray.empty, genGpuCmd.sound_complete.complete _ (by decide)⟩,
    genGpuCmd.sound_complete.complete _ (by decide),
    ⟨⟨#[0]⟩, by decide, genGpuCmd.sound_complete.complete _ (by decide)⟩,
    genGpuCmd.sound_complete.complete _ (by decide),
    ⟨⟨0, 0, 0⟩, genGpuCmd.sound_complete.complete _ (by decide)⟩⟩

/-! ## Saved games -/

/-- **A save that does not load**: one with a hole in the bedrock floor. -/
theorem genSaveData_covers_unloadable :
    ∃ d ∈ SPMF.support genSaveData, d.restore? = none := by
  refine ⟨(⟨0, { pos := ⟨0, 0, 0⟩ }, {}, 0, [(⟨0, 0, 0⟩, .stone)]⟩ : SaveData),
    genSaveData.sound_complete.complete _ (by decide), ?_⟩
  simp [SaveData.restore?]

/--
**A save that does load**: a player falling from far above everything, with
nothing in hand, in an untouched world. So the generator reaches both sides of
every check loading makes.
-/
theorem genSaveData_covers_loadable :
    ∃ d ∈ SPMF.support genSaveData, d.restore?.isSome = true := by
  refine ⟨(⟨0, { pos := ⟨0, 1000000000000000000000, 0⟩ }, {}, 0, []⟩ : SaveData),
    genSaveData.sound_complete.complete _ (by decide), ?_⟩
  -- Nothing is generated that high, so a player there is clear of every block.
  have hfree : ∀ pos : Vec3, 100000000000000000000 ≤ pos.y →
      Player.blocked (Terrain.world 0).solid pos = false := by
    intro pos hy
    refine Player.blocked_eq_false_iff.mpr fun q hq => ?_
    have hq' : Terrain.maxHeight + Terrain.maxTreeHeight < q.y := by
      simp only [Box.Overlaps, Player.box, Player.height, Terrain.maxHeight,
        Terrain.maxTreeHeight] at hq ⊢
      omega
    simp [World.solid, Terrain.generate_above 0 hq', Block.isSolid]
  unfold SaveData.restore?
  split
  · unfold Session.start?
    split
    · rfl
    · next h =>
      exact absurd ⟨hfree _ (by decide), by decide, by decide,
        (hfree _ (by decide)).symm, by decide, by decide⟩ h
  · next h => exact absurd rfl h

end PropTest
