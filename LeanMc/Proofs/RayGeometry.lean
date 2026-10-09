import LeanMc.Core.Ray
import LeanMc.Proofs.Ray

/-!
# The targeting walk follows the segment

`Ray.cast` walks from cell to cell, at each one leaving through the face the
segment from `o` to `o + d` reaches first. Shown here: **every cell the walk
visits is touched by that segment.**

* `Touches o d c` says the segment has a point in the closed cell `c`. The
  point is named by its time along the segment, a fraction `n / m` between 0
  and 1, so the statement is about integers only.
* `Path solid o d a b` is a chain of face-adjacent cells from `a` to `b` in
  which every cell is touched by the segment and every cell before `b` is not
  solid. `cast_path` gives such a chain from the eye's cell to the target,
  `cast_touches` says the target itself is touched, and `cast_none_path` gives
  the chain to the far end of the segment when nothing is targeted.
* `TimedPath` also records the time at which each cell is touched, and
  requires those times never to decrease: the walk does not double back along
  the segment. `cast_timed` and `cast_none_timed` are the stronger forms.

Cells are closed because the walk can visit a cell the segment only grazes.
When the segment passes exactly through an edge or a corner, two faces are
reached at the same time and the walk takes them one after the other, through
a cell that the segment meets in that one point.

The time recorded for a cell is the time the segment crossed the face the walk
came in through, and 0 for the first cell. The argument is `onCourse_step`:
the segment is in the cell at some time, so it reaches none of the faces it
has yet to cross before then, and the walk leaves by the first of them.
-/

namespace LeanMc.Ray

/-- The segment from `o` to `o + d` has a point in the closed cell `c`. -/
def Touches (o d : Vec3) (c : BlockPos) : Prop :=
  ∃ n m : Int, 0 < m ∧ 0 ≤ n ∧ n ≤ m ∧
    c.x * 65536 * m ≤ o.x * m + d.x * n ∧ o.x * m + d.x * n ≤ (c.x + 1) * 65536 * m ∧
    c.y * 65536 * m ≤ o.y * m + d.y * n ∧ o.y * m + d.y * n ≤ (c.y + 1) * 65536 * m ∧
    c.z * 65536 * m ≤ o.z * m + d.z * n ∧ o.z * m + d.z * n ≤ (c.z + 1) * 65536 * m

/-- At time `n / m`, a fraction of the way along it, the segment is in the closed cell `c`. -/
def TouchesAt (o d : Vec3) (c : BlockPos) (n m : Int) : Prop :=
  0 < m ∧ 0 ≤ n ∧ n ≤ m ∧
    c.x * 65536 * m ≤ o.x * m + d.x * n ∧ o.x * m + d.x * n ≤ (c.x + 1) * 65536 * m ∧
    c.y * 65536 * m ≤ o.y * m + d.y * n ∧ o.y * m + d.y * n ≤ (c.y + 1) * 65536 * m ∧
    c.z * 65536 * m ≤ o.z * m + d.z * n ∧ o.z * m + d.z * n ≤ (c.z + 1) * 65536 * m

theorem TouchesAt.touches {o d : Vec3} {c : BlockPos} {n m : Int} (h : TouchesAt o d c n m) :
    Touches o d c :=
  ⟨n, m, h⟩

/-- The segment starts in the cell the walk starts in. -/
theorem touchesAt_blockPos (o d : Vec3) : TouchesAt o d o.blockPos 0 1 := by
  simp only [TouchesAt, Vec3.blockPos]
  omega

/-- **The walk starts on the segment**: the eye's cell is touched, at time 0. -/
theorem touches_blockPos (o d : Vec3) : Touches o d o.blockPos :=
  (touchesAt_blockPos o d).touches

namespace Geometry

/-! ## Fractions -/

/-- `sooner` is transitive on fractions with positive denominators, here spelled out. -/
theorem frac_le_trans {a b c d e f : Int} (hb : 0 < b) (hd : 0 < d) (hf : 0 < f)
    (h1 : a * d ≤ c * b) (h2 : c * f ≤ e * d) : a * f ≤ e * b := by
  have h3 := Int.mul_le_mul_of_nonneg_right h1 (Int.le_of_lt hf)
  have h4 := Int.mul_le_mul_of_nonneg_right h2 (Int.le_of_lt hb)
  have h5 : d * (a * f) ≤ d * (e * b) := by grind
  exact Int.le_of_mul_le_mul_left h5 hd

theorem sooner_iff {p q : Int × Int} : sooner p q = true ↔ p.1 * q.2 ≤ q.1 * p.2 := by
  simp only [sooner, decide_eq_true_eq]

theorem sooner_trans {p q r : Int × Int} (hp : 0 < p.2) (hq : 0 < q.2) (hr : 0 < r.2)
    (h1 : sooner p q = true) (h2 : sooner q r = true) : sooner p r = true := by
  simp only [sooner_iff] at *
  exact frac_le_trans hp hq hr h1 h2

theorem sooner_total {p q : Int × Int} (h : ¬sooner p q = true) : sooner q p = true := by
  simp only [sooner_iff] at *
  exact Int.le_of_lt (Int.not_le.mp h)

/-! ## One axis at a time -/

/--
Along an axis the walk is not stepping on. The segment is between the planes
`lo` and `hi` at time `n / m`, and `num / den` is a later time, no later than
the time it reaches whichever of the two planes it goes on past. Then it is
still between them at time `num / den`.
-/
theorem axis_keep {lo hi oa da n m num den : Int} (hm : 0 < m) (hden : 0 < den)
    (h1 : num ≤ den) (hlate : n * den ≤ num * m)
    (hlo : lo * m ≤ oa * m + da * n) (hhi : oa * m + da * n ≤ hi * m)
    (hup : hi ≤ oa + da → num * da ≤ (hi - oa) * den)
    (hdn : oa + da < lo → num * -da ≤ (oa - lo) * den) :
    lo * den ≤ oa * den + da * num ∧ oa * den + da * num ≤ hi * den := by
  constructor
  · by_cases hc : oa + da < lo
    · have := hdn hc
      grind
    · by_cases hs : 0 ≤ da
      · have h2 := Int.mul_le_mul_of_nonneg_left hlate hs
        have h3 := Int.mul_le_mul_of_nonneg_right hlo (Int.le_of_lt hden)
        have h4 : m * (lo * den) ≤ m * (oa * den + da * num) := by grind
        exact Int.le_of_mul_le_mul_left h4 hm
      · have h2 := Int.mul_le_mul_of_nonpos_left (Int.le_of_lt (Int.not_le.mp hs)) h1
        have h3 : lo * den ≤ (oa + da) * den :=
          Int.mul_le_mul_of_nonneg_right (Int.not_lt.mp hc) (Int.le_of_lt hden)
        grind
  · by_cases hc : hi ≤ oa + da
    · have := hup hc
      grind
    · by_cases hs : 0 ≤ da
      · have h2 := Int.mul_le_mul_of_nonneg_left h1 hs
        have h3 : (oa + da) * den ≤ hi * den :=
          Int.mul_le_mul_of_nonneg_right (Int.le_of_lt (Int.not_le.mp hc)) (Int.le_of_lt hden)
        grind
      · have h2 := Int.mul_le_mul_of_nonpos_left (Int.le_of_lt (Int.not_le.mp hs)) hlate
        have h3 := Int.mul_le_mul_of_nonneg_right hhi (Int.le_of_lt hden)
        have h4 : m * (oa * den + da * num) ≤ m * (hi * den) := by grind
        exact Int.le_of_mul_le_mul_left h4 hm

/--
Along the axis the walk steps up on. The crossing time is no earlier than any
time the segment is still below the face, and at the crossing time the segment
is on the face, so in the closed cell on the other side.
-/
theorem axis_up {oa da ca n m : Int} (hd : 0 < da)
    (hhi : oa * m + da * n ≤ (ca + 1) * 65536 * m) :
    n * da ≤ ((ca + 1) * 65536 - oa) * m
      ∧ (ca + 1) * 65536 * da ≤ oa * da + da * ((ca + 1) * 65536 - oa)
      ∧ oa * da + da * ((ca + 1) * 65536 - oa) ≤ (ca + 1 + 1) * 65536 * da := by
  grind

/-- Along the axis the walk steps down on; the mirror image of `axis_up`. -/
theorem axis_down {oa da ca n m : Int} (hd : 0 < -da)
    (hlo : ca * 65536 * m ≤ oa * m + da * n) :
    n * -da ≤ (oa - ca * 65536) * m
      ∧ (ca - 1) * 65536 * -da ≤ oa * -da + da * (oa - ca * 65536)
      ∧ oa * -da + da * (oa - ca * 65536) ≤ (ca - 1 + 1) * 65536 * -da := by
  grind

/-! ## The walk leaves by the face reached first -/

/-- The cell `c` lies in the box of cells spanned by the two ends of the segment. -/
def Boxed (o d : Vec3) (c : BlockPos) : Prop :=
  (o.x / 65536 ≤ c.x ∧ c.x ≤ (o.x + d.x) / 65536
    ∨ (o.x + d.x) / 65536 ≤ c.x ∧ c.x ≤ o.x / 65536) ∧
  (o.y / 65536 ≤ c.y ∧ c.y ≤ (o.y + d.y) / 65536
    ∨ (o.y + d.y) / 65536 ≤ c.y ∧ c.y ≤ o.y / 65536) ∧
  (o.z / 65536 ≤ c.z ∧ c.z ≤ (o.z + d.z) / 65536
    ∨ (o.z + d.z) / 65536 ≤ c.z ∧ c.z ≤ o.z / 65536)

theorem boxed_blockPos (o d : Vec3) : Boxed o d o.blockPos := by
  simp only [Boxed, Vec3.blockPos]
  omega

theorem boxed_step {o d : Vec3} {c : BlockPos} {dir : Dir} (hb : Boxed o d c)
    (hc : crosses o d c dir = true) : Boxed o d (c.step dir) := by
  cases dir <;> simp only [crosses, decide_eq_true_eq, Boxed, BlockPos.step] at * <;> omega

/--
Inside the box, the time at which the segment reaches a face it goes on past
is a fraction between 0 and 1 with a positive denominator: the segment is not
parallel to the face, it starts on the near side and it ends on or beyond it.
-/
theorem crossTime_bounds {o d : Vec3} {c : BlockPos} {dir : Dir} (hb : Boxed o d c)
    (hc : crosses o d c dir = true) :
    0 < (crossTime o d c dir).2 ∧ 0 ≤ (crossTime o d c dir).1
      ∧ (crossTime o d c dir).1 ≤ (crossTime o d c dir).2 := by
  cases dir <;> simp only [crosses, crossTime, decide_eq_true_eq, Boxed] at * <;> omega

/-- Picking the earliest exit from a list of candidates returns one of the candidates. -/
theorem pick_mem (o d : Vec3) (c : BlockPos) (l : List Dir) (best : Option Dir) {r : Dir}
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

/-- Picking the earliest exit yields nothing only when there were no candidates. -/
theorem pick_none (o d : Vec3) (c : BlockPos) (l : List Dir) (best : Option Dir)
    (h : l.foldl (pick o d c) best = none) : best = none ∧ l = [] := by
  induction l generalizing best with
  | nil => exact ⟨h, rfl⟩
  | cons a l ih =>
    have := (ih _ h).1
    unfold pick at this
    split at this
    · cases this
    · split at this <;> cases this

/--
Picking the earliest exit from candidates whose crossing times all have
positive denominators returns one that is no later than every candidate.
-/
theorem pick_sooner (o d : Vec3) (c : BlockPos) (l : List Dir) (best : Option Dir) {r : Dir}
    (hl : ∀ e ∈ l, 0 < (crossTime o d c e).2)
    (hb : ∀ b, best = some b → 0 < (crossTime o d c b).2)
    (h : l.foldl (pick o d c) best = some r) :
    (∀ b, best = some b → sooner (crossTime o d c r) (crossTime o d c b) = true)
      ∧ ∀ e ∈ l, sooner (crossTime o d c r) (crossTime o d c e) = true := by
  induction l generalizing best with
  | nil =>
    cases h
    refine ⟨?_, fun e he => nomatch he⟩
    intro b hbr
    cases hbr
    exact sooner_iff.mpr (Int.le_refl _)
  | cons a l ih =>
    have hr : 0 < (crossTime o d c r).2 := by
      rcases pick_mem o d c _ best h with h' | h'
      · exact hb r h'
      · exact hl r h'
    have ha := hl a List.mem_cons_self
    have hl' : ∀ e ∈ l, 0 < (crossTime o d c e).2 :=
      fun e he => hl e (List.mem_cons_of_mem _ he)
    rw [List.foldl_cons] at h
    cases best with
    | none =>
      obtain ⟨h1, h2⟩ := ih (some a) hl' (fun b hba => by cases hba; exact ha) h
      refine ⟨fun b hbn => (nomatch hbn), ?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact h1 _ rfl
      · exact h2 e he
    | some b =>
      have hb' := hb b rfl
      by_cases hs : sooner (crossTime o d c b) (crossTime o d c a) = true
      · have hp : pick o d c (some b) a = some b := by simp [pick, hs]
        rw [hp] at h
        obtain ⟨h1, h2⟩ := ih (some b) hl' hb h
        have hrb := h1 b rfl
        refine ⟨fun b' hbb => by cases hbb; exact hrb, ?_⟩
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact sooner_trans hr hb' ha hrb hs
        · exact h2 e he
      · have hp : pick o d c (some b) a = some a := by simp [pick, hs]
        rw [hp] at h
        obtain ⟨h1, h2⟩ := ih (some a) hl' (fun b hba => by cases hba; exact ha) h
        have hra := h1 a rfl
        refine ⟨fun b' hbb => ?_, ?_⟩
        · cases hbb
          exact sooner_trans hr ha hb' hra (sooner_total hs)
        · intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact hra
          · exact h2 e he

/-- The walk only leaves a cell through a face the segment really goes on past. -/
theorem crosses_of_nextStep {o d : Vec3} {c : BlockPos} {dir : Dir}
    (h : nextStep o d c = some dir) : crosses o d c dir = true := by
  unfold nextStep at h
  rcases pick_mem o d c _ none h with h' | h'
  · cases h'
  · exact (List.mem_filter.mp h').2

/-- Of the faces the segment goes on past, the walk leaves through one it reaches first. -/
theorem nextStep_sooner {o d : Vec3} {c : BlockPos} {dir : Dir} (hb : Boxed o d c)
    (h : nextStep o d c = some dir) {e : Dir} (he : crosses o d c e = true) :
    sooner (crossTime o d c dir) (crossTime o d c e) = true := by
  unfold nextStep at h
  refine (pick_sooner o d c _ none ?_ (fun b hbn => nomatch hbn) h).2 e ?_
  · intro e' he'
    exact (crossTime_bounds hb (List.mem_filter.mp he').2).1
  · exact List.mem_filter.mpr ⟨by cases e <;> decide, he⟩

/-- Each step of the walk brings it one cell closer to the far end of the segment. -/
theorem remaining_of_crosses {o d : Vec3} {c : BlockPos} {dir : Dir}
    (h : crosses o d c dir = true) : remaining o d (c.step dir) + 1 = remaining o d c := by
  cases dir <;> simp only [crosses, decide_eq_true_eq, remaining, BlockPos.step] at h ⊢ <;> omega

/-- The walk stops for want of a next cell only in the cell holding the segment's far end. -/
theorem blockPos_of_no_nextStep {o d : Vec3} {c : BlockPos} (h : nextStep o d c = none) :
    c = (⟨o.x + d.x, o.y + d.y, o.z + d.z⟩ : Vec3).blockPos := by
  have hempty := (pick_none o d c _ none h).2
  have hno : ∀ dir, crosses o d c dir = false := by
    intro dir
    cases hc : crosses o d c dir
    · rfl
    · have : dir ∈ Dir.all.filter (crosses o d c) :=
        List.mem_filter.mpr ⟨by cases dir <;> decide, hc⟩
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

end Geometry

open Geometry

/-! ## The invariant of the walk -/

/--
What the walk keeps true of the cell `c` it is in: the segment is in the
closed cell at time `n / m`, and the cell lies in the box of cells spanned by
the segment's two ends. The second part is what makes the crossing times of
the faces still to be crossed honest fractions.
-/
def OnCourse (o d : Vec3) (c : BlockPos) (n m : Int) : Prop :=
  TouchesAt o d c n m ∧ Boxed o d c

theorem OnCourse.touches {o d : Vec3} {c : BlockPos} {n m : Int} (h : OnCourse o d c n m) :
    Touches o d c :=
  h.1.touches

/-- The walk starts on course, at time 0. -/
theorem onCourse_blockPos (o d : Vec3) : OnCourse o d o.blockPos 0 1 :=
  ⟨touchesAt_blockPos o d, boxed_blockPos o d⟩

/--
**Each step stays on the segment.** If the segment is in cell `c` at time
`n / m` and the walk leaves through face `dir`, then at the time it crosses
that face the segment is in the next cell, and that time is no earlier than
`n / m`.
-/
theorem onCourse_step {o d : Vec3} {c : BlockPos} {n m : Int} {dir : Dir}
    (hi : OnCourse o d c n m) (h : nextStep o d c = some dir) :
    OnCourse o d (c.step dir) (crossTime o d c dir).1 (crossTime o d c dir).2
      ∧ n * (crossTime o d c dir).2 ≤ (crossTime o d c dir).1 * m := by
  obtain ⟨⟨hm, -, -, hx0, hx1, hy0, hy1, hz0, hz1⟩, hb⟩ := hi
  have hc := crosses_of_nextStep h
  obtain ⟨hden, hnum0, hnum1⟩ := crossTime_bounds hb hc
  have hxp := @nextStep_sooner o d c dir hb h .xp
  have hxn := @nextStep_sooner o d c dir hb h .xn
  have hyp := @nextStep_sooner o d c dir hb h .yp
  have hyn := @nextStep_sooner o d c dir hb h .yn
  have hzp := @nextStep_sooner o d c dir hb h .zp
  have hzn := @nextStep_sooner o d c dir hb h .zn
  refine ⟨⟨?_, boxed_step hb hc⟩, ?_⟩
  all_goals
    cases dir <;>
      simp only [crosses, crossTime, sooner_iff, decide_eq_true_eq, TouchesAt, BlockPos.step] at *
  · obtain ⟨hlate, hx0', hx1'⟩ := axis_up hden hx1
    obtain ⟨hy0', hy1'⟩ := axis_keep hm hden hnum1 hlate hy0 hy1 hyp hyn
    obtain ⟨hz0', hz1'⟩ := axis_keep hm hden hnum1 hlate hz0 hz1 hzp hzn
    exact ⟨hden, hnum0, hnum1, hx0', hx1', hy0', hy1', hz0', hz1'⟩
  · obtain ⟨hlate, hx0', hx1'⟩ := axis_down hden hx0
    obtain ⟨hy0', hy1'⟩ := axis_keep hm hden hnum1 hlate hy0 hy1 hyp hyn
    obtain ⟨hz0', hz1'⟩ := axis_keep hm hden hnum1 hlate hz0 hz1 hzp hzn
    exact ⟨hden, hnum0, hnum1, hx0', hx1', hy0', hy1', hz0', hz1'⟩
  · obtain ⟨hlate, hy0', hy1'⟩ := axis_up hden hy1
    obtain ⟨hx0', hx1'⟩ := axis_keep hm hden hnum1 hlate hx0 hx1 hxp hxn
    obtain ⟨hz0', hz1'⟩ := axis_keep hm hden hnum1 hlate hz0 hz1 hzp hzn
    exact ⟨hden, hnum0, hnum1, hx0', hx1', hy0', hy1', hz0', hz1'⟩
  · obtain ⟨hlate, hy0', hy1'⟩ := axis_down hden hy0
    obtain ⟨hx0', hx1'⟩ := axis_keep hm hden hnum1 hlate hx0 hx1 hxp hxn
    obtain ⟨hz0', hz1'⟩ := axis_keep hm hden hnum1 hlate hz0 hz1 hzp hzn
    exact ⟨hden, hnum0, hnum1, hx0', hx1', hy0', hy1', hz0', hz1'⟩
  · obtain ⟨hlate, hz0', hz1'⟩ := axis_up hden hz1
    obtain ⟨hx0', hx1'⟩ := axis_keep hm hden hnum1 hlate hx0 hx1 hxp hxn
    obtain ⟨hy0', hy1'⟩ := axis_keep hm hden hnum1 hlate hy0 hy1 hyp hyn
    exact ⟨hden, hnum0, hnum1, hx0', hx1', hy0', hy1', hz0', hz1'⟩
  · obtain ⟨hlate, hz0', hz1'⟩ := axis_down hden hz0
    obtain ⟨hx0', hx1'⟩ := axis_keep hm hden hnum1 hlate hx0 hx1 hxp hxn
    obtain ⟨hy0', hy1'⟩ := axis_keep hm hden hnum1 hlate hy0 hy1 hyp hyn
    exact ⟨hden, hnum0, hnum1, hx0', hx1', hy0', hy1', hz0', hz1'⟩
  · exact (axis_up hden hx1).1
  · exact (axis_down hden hx0).1
  · exact (axis_up hden hy1).1
  · exact (axis_down hden hy0).1
  · exact (axis_up hden hz1).1
  · exact (axis_down hden hz0).1

/-! ## Paths along the segment -/

/--
A chain of face-adjacent cells from `a` to `b`, every one of them touched by
the segment from `o` to `o + d`, and every one before `b` not solid.
-/
inductive Path (solid : BlockPos → Bool) (o d : Vec3) : BlockPos → BlockPos → Prop
  | here (c : BlockPos) : Touches o d c → Path solid o d c c
  | step {a b : BlockPos} (dir : Dir) :
    solid a = false → Touches o d a → Path solid o d (a.step dir) b → Path solid o d a b

/--
A `Path` that also says when each cell is touched. `TimedPath solid o d a n m b`
starts in cell `a`, where the segment is at time `n / m`, and each step goes to
a cell where the segment is at a time no earlier than the one before.
-/
inductive TimedPath (solid : BlockPos → Bool) (o d : Vec3) :
    BlockPos → Int → Int → BlockPos → Prop
  | here {c : BlockPos} {n m : Int} : TouchesAt o d c n m → TimedPath solid o d c n m c
  | step {a b : BlockPos} {n m n' m' : Int} (dir : Dir) :
    solid a = false → TouchesAt o d a n m → n * m' ≤ n' * m →
    TimedPath solid o d (a.step dir) n' m' b → TimedPath solid o d a n m b

variable {solid : BlockPos → Bool} {o d : Vec3}

/-- Forgetting the times leaves a path. -/
theorem TimedPath.path {a b : BlockPos} {n m : Int} (h : TimedPath solid o d a n m b) :
    Path solid o d a b := by
  induction h with
  | here ht => exact .here _ ht.touches
  | step dir hs ht _ _ ih => exact .step dir hs ht.touches ih

/-- The last cell of a path is touched by the segment, like all the others. -/
theorem Path.touches {a b : BlockPos} (h : Path solid o d a b) : Touches o d b := by
  induction h with
  | here _ ht => exact ht
  | step _ _ _ _ ih => exact ih

theorem castFrom_timed {fuel : Nat} {c : BlockPos} {entered : Option Dir} {hit : RayHit}
    {n m : Int} (hi : OnCourse o d c n m) (h : castFrom solid o d fuel c entered = some hit) :
    TimedPath solid o d c n m hit.block := by
  induction fuel generalizing c entered n m with
  | zero => cases h
  | succ fuel ih =>
    unfold castFrom at h
    split at h
    · cases h
      exact .here hi.1
    · next hs =>
      split at h
      · cases h
      · next dir hn =>
        obtain ⟨hi', hle⟩ := onCourse_step hi hn
        exact .step dir (by simpa using hs) hi.1 hle (ih hi' h)

theorem castFrom_none_timed {fuel : Nat} {c : BlockPos} {entered : Option Dir} {n m : Int}
    (hi : OnCourse o d c n m) (hf : remaining o d c < fuel)
    (h : castFrom solid o d fuel c entered = none) :
    TimedPath solid o d c n m (⟨o.x + d.x, o.y + d.y, o.z + d.z⟩ : Vec3).blockPos
      ∧ solid (⟨o.x + d.x, o.y + d.y, o.z + d.z⟩ : Vec3).blockPos = false := by
  induction fuel generalizing c entered n m with
  | zero => omega
  | succ fuel ih =>
    unfold castFrom at h
    split at h
    · cases h
    · next hs =>
      split at h
      · next hn =>
        rw [← blockPos_of_no_nextStep hn]
        exact ⟨.here hi.1, by simpa using hs⟩
      · next dir hn =>
        have hstep := remaining_of_crosses (crosses_of_nextStep hn)
        obtain ⟨hi', hle⟩ := onCourse_step hi hn
        obtain ⟨hw, hend⟩ := ih hi' (by omega) h
        exact ⟨.step dir (by simpa using hs) hi.1 hle hw, hend⟩

/--
**The walk never doubles back.** The chain of cells from the eye to the target
can be given times, starting at 0 and never decreasing, at which the segment
is in each cell in turn.
-/
theorem cast_timed {hit : RayHit} (h : cast solid o d = some hit) :
    TimedPath solid o d o.blockPos 0 1 hit.block :=
  castFrom_timed (onCourse_blockPos o d) h

/--
**The walk follows the segment.** The target is reached from the eye's cell by
a chain of face-adjacent cells, every one of them touched by the segment from
`o` to `o + d` and every one before the target empty.
-/
theorem cast_path {hit : RayHit} (h : cast solid o d = some hit) :
    Path solid o d o.blockPos hit.block :=
  (cast_timed h).path

/-- **The target is on the line of sight**: the segment touches the targeted block. -/
theorem cast_touches {hit : RayHit} (h : cast solid o d = some hit) : Touches o d hit.block :=
  (cast_path h).touches

/-- If no block is targeted, the walk went to the far end of the segment without doubling back. -/
theorem cast_none_timed (h : cast solid o d = none) :
    TimedPath solid o d o.blockPos 0 1 (⟨o.x + d.x, o.y + d.y, o.z + d.z⟩ : Vec3).blockPos
      ∧ solid (⟨o.x + d.x, o.y + d.y, o.z + d.z⟩ : Vec3).blockPos = false :=
  castFrom_none_timed (onCourse_blockPos o d) (Nat.lt_succ_self _) h

/--
**Nothing along the segment is missed.** If no block is targeted, the walk
went all the way to the cell at the far end of the segment, through empty
cells that the segment touches, however long the segment.
-/
theorem cast_none_path (h : cast solid o d = none) :
    Path solid o d o.blockPos (⟨o.x + d.x, o.y + d.y, o.z + d.z⟩ : Vec3).blockPos
      ∧ solid (⟨o.x + d.x, o.y + d.y, o.z + d.z⟩ : Vec3).blockPos = false :=
  ⟨(cast_none_timed h).1.path, (cast_none_timed h).2⟩

/-- A path is in particular a walk: forgetting that its cells are touched leaves the chain. -/
theorem Path.walk {solid : BlockPos → Bool} {o d : Vec3} {a b : BlockPos}
    (h : Path solid o d a b) : Walk solid a b := by
  induction h with
  | here c _ => exact .here c
  | step dir hs _ _ ih => exact .step dir hs ih

end LeanMc.Ray
