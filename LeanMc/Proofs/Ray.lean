import LeanMc.Core.Ray
import LeanMc.Proofs.Mesh

/-!
# Targeting theorems

* **The target is solid.**
* **The cell in front of the targeted face is empty**, and it is face-adjacent
  to the target by construction. So a block placed there never replaces one.
* **Nothing solid comes first.** The target is reached from the eye's cell by a
  chain of face-adjacent cells, every one of which before the target is empty.
* **The target is within reach**: inside the box of cells spanned by the two
  ends of the segment that was walked, and so is the cell in front of its face.
* **Only a walk that starts inside a block has no face to report.**

These are properties of the walk the targeting code takes. That the walk
follows the geometric segment, every cell it visits being one the segment
touches, is shown in `LeanMc.Proofs.RayGeometry`.
-/

namespace LeanMc.Ray

/-- Picking the earliest exit from a list of candidates returns one of the candidates. -/
theorem foldl_pick (o d : Vec3) (c : BlockPos) (l : List Dir) (best : Option Dir) {r : Dir}
    (h : l.foldl (pick o d c) best = some r) : best = some r ∨ r ∈ l := by
  induction l generalizing best with
  | nil => exact .inl h
  | cons a l ih =>
    rcases ih _ h with h' | h'
    · unfold pick at h'
      split at h'
      · cases h'
        exact .inr List.mem_cons_self
      · split at h'
        · exact .inl h'
        · cases h'
          exact .inr List.mem_cons_self
    · exact .inr (List.mem_cons_of_mem _ h')

/-- The walk only leaves a cell through a face the segment really goes on past. -/
theorem nextStep_crosses {o d : Vec3} {c : BlockPos} {dir : Dir} (h : nextStep o d c = some dir) :
    crosses o d c dir = true := by
  unfold nextStep at h
  rcases foldl_pick o d c _ none h with h' | h'
  · cases h'
  · exact (List.mem_filter.mp h').2

/-- A chain of face-adjacent cells from `a` to `b` in which every cell before `b` is not solid. -/
inductive Walk (solid : BlockPos → Bool) : BlockPos → BlockPos → Prop
  | here (c : BlockPos) : Walk solid c c
  | step {a b : BlockPos} (dir : Dir) : solid a = false → Walk solid (a.step dir) b → Walk solid a b

/-- The cell `c` lies in the box of cells spanned by the two ends of the segment. -/
def Within (o d : Vec3) (c : BlockPos) : Prop :=
  (o.x / 65536 ≤ c.x ∨ (o.x + d.x) / 65536 ≤ c.x) ∧ (c.x ≤ o.x / 65536 ∨ c.x ≤ (o.x + d.x) / 65536) ∧
  (o.y / 65536 ≤ c.y ∨ (o.y + d.y) / 65536 ≤ c.y) ∧ (c.y ≤ o.y / 65536 ∨ c.y ≤ (o.y + d.y) / 65536) ∧
  (o.z / 65536 ≤ c.z ∨ (o.z + d.z) / 65536 ≤ c.z) ∧ (c.z ≤ o.z / 65536 ∨ c.z ≤ (o.z + d.z) / 65536)

theorem within_blockPos (o d : Vec3) : Within o d o.blockPos := by
  simp only [Within, Vec3.blockPos]
  omega

theorem within_step {o d : Vec3} {c : BlockPos} {dir : Dir} (hw : Within o d c)
    (hc : crosses o d c dir = true) : Within o d (c.step dir) := by
  cases dir <;> simp only [crosses, decide_eq_true_eq, Within, BlockPos.step] at * <;> omega

variable {solid : BlockPos → Bool} {o d : Vec3}

theorem castFrom_solid {fuel : Nat} {c : BlockPos} {entered : Option Dir} {hit : RayHit}
    (h : castFrom solid o d fuel c entered = some hit) : solid hit.block = true := by
  induction fuel generalizing c entered with
  | zero => cases h
  | succ fuel ih =>
    unfold castFrom at h
    split at h
    · next hs =>
      cases h
      exact hs
    · split at h
      · cases h
      · exact ih h

theorem castFrom_walk {fuel : Nat} {c : BlockPos} {entered : Option Dir} {hit : RayHit}
    (h : castFrom solid o d fuel c entered = some hit) : Walk solid c hit.block := by
  induction fuel generalizing c entered with
  | zero => cases h
  | succ fuel ih =>
    unfold castFrom at h
    split at h
    · cases h
      exact .here _
    · next hs =>
      split at h
      · cases h
      · exact .step _ (by simpa using hs) (ih h)

theorem castFrom_face {fuel : Nat} {c : BlockPos} {entered : Option Dir} {hit : RayHit}
    (hent : ∀ dir, entered = some dir → solid (c.step dir.opp) = false)
    (h : castFrom solid o d fuel c entered = some hit) {f : Dir} (hf : hit.face = some f) :
    solid (hit.block.step f) = false := by
  induction fuel generalizing c entered with
  | zero => cases h
  | succ fuel ih =>
    unfold castFrom at h
    split at h
    · cases h
      cases entered with
      | none => cases hf
      | some dir =>
        cases hf
        exact hent dir rfl
    · next hs =>
      split at h
      · cases h
      · next dir _ =>
        refine ih ?_ h
        intro dir' hd
        cases hd
        rw [BlockPos.step_step_opp]
        simpa using hs

theorem castFrom_within {fuel : Nat} {c : BlockPos} {entered : Option Dir} {hit : RayHit}
    (hw : Within o d c) (h : castFrom solid o d fuel c entered = some hit) :
    Within o d hit.block := by
  induction fuel generalizing c entered with
  | zero => cases h
  | succ fuel ih =>
    unfold castFrom at h
    split at h
    · cases h
      exact hw
    · split at h
      · cases h
      · next hn => exact ih (within_step hw (nextStep_crosses hn)) h

/-! ## The walk never stops early -/

/-- Each step of the walk brings it one cell closer to the far end of the segment. -/
theorem remaining_step {o d : Vec3} {c : BlockPos} {dir : Dir} (h : crosses o d c dir = true) :
    remaining o d (c.step dir) + 1 = remaining o d c := by
  cases dir <;> simp only [crosses, decide_eq_true_eq, remaining, BlockPos.step] at h ⊢ <;> omega

theorem foldl_pick_none (o d : Vec3) (c : BlockPos) (l : List Dir) (best : Option Dir)
    (h : l.foldl (pick o d c) best = none) : best = none ∧ l = [] := by
  induction l generalizing best with
  | nil => exact ⟨h, rfl⟩
  | cons a l ih =>
    have := (ih _ h).1
    unfold pick at this
    split at this
    · cases this
    · split at this <;> cases this

/-- The walk stops for want of a next cell only in the cell holding the segment's far end. -/
theorem blockPos_of_nextStep_none {o d : Vec3} {c : BlockPos} (h : nextStep o d c = none) :
    c = (⟨o.x + d.x, o.y + d.y, o.z + d.z⟩ : Vec3).blockPos := by
  have hempty := (foldl_pick_none o d c _ none h).2
  have hno : ∀ dir, crosses o d c dir = false := by
    intro dir
    cases hc : crosses o d c dir
    · rfl
    · have : dir ∈ Dir.all.filter (crosses o d c) := List.mem_filter.mpr ⟨Dir.mem_all dir, hc⟩
      rw [hempty] at this
      cases this
  have hxp := hno .xp
  have hxn := hno .xn
  have hyp := hno .yp
  have hyn := hno .yn
  have hzp := hno .zp
  have hzn := hno .zn
  simp only [crosses, decide_eq_false_iff_not] at hxp hxn hyp hyn hzp hzn
  ext <;> simp only [Vec3.blockPos] <;> omega

/-- With fuel for every cell it could enter, the walk gives up only at the segment's far end. -/
theorem castFrom_none {fuel : Nat} {c : BlockPos} {entered : Option Dir}
    (hf : remaining o d c < fuel) (h : castFrom solid o d fuel c entered = none) :
    Walk solid c (⟨o.x + d.x, o.y + d.y, o.z + d.z⟩ : Vec3).blockPos
      ∧ solid (⟨o.x + d.x, o.y + d.y, o.z + d.z⟩ : Vec3).blockPos = false := by
  induction fuel generalizing c entered with
  | zero => omega
  | succ fuel ih =>
    unfold castFrom at h
    split at h
    · cases h
    · next hs =>
      split at h
      · next hn =>
        rw [← blockPos_of_nextStep_none hn]
        exact ⟨.here _, by simpa using hs⟩
      · next dir hn =>
        have hstep := remaining_step (nextStep_crosses hn)
        obtain ⟨hw, hend⟩ := ih (by omega) h
        exact ⟨.step dir (by simpa using hs) hw, hend⟩

/--
**Nothing is missed for want of looking.** If no block is targeted, the walk
went all the way to the cell at the far end of the segment, through cells that
were all empty, however long the segment.
-/
theorem cast_none (h : cast solid o d = none) :
    Walk solid o.blockPos (⟨o.x + d.x, o.y + d.y, o.z + d.z⟩ : Vec3).blockPos
      ∧ solid (⟨o.x + d.x, o.y + d.y, o.z + d.z⟩ : Vec3).blockPos = false :=
  castFrom_none (Nat.lt_succ_self _) h

/-- **The target is solid.** -/
theorem cast_solid {hit : RayHit} (h : cast solid o d = some hit) : solid hit.block = true :=
  castFrom_solid h

/--
**The cell in front of the targeted face is empty.** That cell is
`hit.block.step f`, one step from the target, so a block placed there is next
to the target and replaces nothing solid.
-/
theorem cast_face_clear {hit : RayHit} (h : cast solid o d = some hit) {f : Dir}
    (hf : hit.face = some f) : solid (hit.block.step f) = false :=
  castFrom_face (fun _ hd => by cases hd) h hf

/-- **Nothing solid comes first**: a chain of empty, face-adjacent cells leads from the eye to the target. -/
theorem cast_walk {hit : RayHit} (h : cast solid o d = some hit) :
    Walk solid o.blockPos hit.block :=
  castFrom_walk h

/-- **The target is within reach**: inside the box of cells spanned by the segment's ends. -/
theorem cast_within {hit : RayHit} (h : cast solid o d = some hit) : Within o d hit.block :=
  castFrom_within (within_blockPos o d) h

/-! ## The targeted face -/

/-- Once the walk has taken a step, whatever it hits has a face. -/
theorem castFrom_face_some {fuel : Nat} {c : BlockPos} {dir : Dir} {hit : RayHit}
    (h : castFrom solid o d fuel c (some dir) = some hit) : hit.face ≠ none := by
  induction fuel generalizing c dir with
  | zero => cases h
  | succ fuel ih =>
    unfold castFrom at h
    split at h
    · cases h
      simp
    · split at h
      · cases h
      · exact ih h

/-- **Only a walk that starts inside a block has no face to report.** -/
theorem cast_face_none {hit : RayHit} (h : cast solid o d = some hit) (hf : hit.face = none) :
    solid o.blockPos = true := by
  unfold cast castFrom at h
  split at h
  · next hs => exact hs
  · split at h
    · cases h
    · exact absurd hf (castFrom_face_some h)

theorem castFrom_face_within {fuel : Nat} {c : BlockPos} {entered : Option Dir} {hit : RayHit}
    (hw : Within o d c) (hent : ∀ dir, entered = some dir → Within o d (c.step dir.opp))
    (h : castFrom solid o d fuel c entered = some hit) {f : Dir} (hf : hit.face = some f) :
    Within o d (hit.block.step f) := by
  induction fuel generalizing c entered with
  | zero => cases h
  | succ fuel ih =>
    unfold castFrom at h
    split at h
    · cases h
      cases entered with
      | none => cases hf
      | some dir =>
        cases hf
        exact hent dir rfl
    · split at h
      · cases h
      · next dir hn =>
        refine ih (within_step hw (nextStep_crosses hn)) ?_ h
        intro dir' hd
        cases hd
        rw [BlockPos.step_step_opp]
        exact hw

/--
**The cell in front of the targeted face is within reach too**: it is the cell
the walk was in just before the target, so it lies in the same box of cells.
-/
theorem cast_face_within {hit : RayHit} (h : cast solid o d = some hit) {f : Dir}
    (hf : hit.face = some f) : Within o d (hit.block.step f) :=
  castFrom_face_within (within_blockPos o d) (fun _ hd => by cases hd) h hf

end LeanMc.Ray
