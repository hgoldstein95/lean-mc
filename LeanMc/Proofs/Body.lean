import LeanMc.Core.Body

/-!
# Body physics theorems

These hold for a body of any shape, so for the player and for every creature.

* **The collision check is exact.** `Box.collides` is false exactly when no
  solid block overlaps the box.
* **No clipping.** A body that is not inside a solid block is still not inside
  one after a move, whatever velocity it attempts.
* **No tunnelling.** A move takes the body through a chain of short,
  axis-aligned substeps, and the body's box is clear of solid blocks at every
  point along every substep, not only at its ends.
* **A move goes the whole way or stops flush.** A move that is not reported as
  blocked ends exactly where it was meant to; one that is leaves the body
  touching what stopped it, with no gap. So "blocked" always means an obstacle.
* **Speed is bounded.** A move never leaves a body faster than it set out, so
  the rounds `moveAxis` is given always suffice.
* **The floor holds.** Over a solid floor at height zero, a body's feet never
  go below the top of that floor.
* **Physics is the same everywhere.** Shifting the world and the body by any
  whole number of blocks commutes with a move. This is false for floating
  point, where precision depends on distance from the origin.
-/

namespace LeanMc

/-! ## Overlap and the collision check -/

namespace Box

/-- No solid block overlaps the box. -/
def Free (solid : BlockPos → Bool) (b : Box) : Prop :=
  ∀ p, b.Overlaps p → solid p = false

end Box

theorem mem_intRange {lo hi n : Int} : n ∈ intRange lo hi ↔ lo ≤ n ∧ n ≤ hi := by
  simp only [intRange, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi', rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨(n - lo).toNat, by omega, by omega⟩

theorem mem_blockRange {lo hi n : Int} :
    n ∈ blockRange lo hi ↔ lo < (n + 1) * 65536 ∧ n * 65536 < hi := by
  rw [blockRange, mem_intRange]
  omega

namespace Box

theorem collides_eq_true_iff {solid : BlockPos → Bool} {b : Box} :
    b.collides solid = true ↔ ∃ p, b.Overlaps p ∧ solid p = true := by
  simp only [collides, List.any_eq_true, mem_blockRange, Overlaps]
  constructor
  · rintro ⟨x, hx, y, hy, z, hz, hs⟩
    exact ⟨⟨x, y, z⟩, ⟨hx.1, hx.2, hy.1, hy.2, hz.1, hz.2⟩, hs⟩
  · rintro ⟨p, ⟨h1, h2, h3, h4, h5, h6⟩, hs⟩
    exact ⟨p.x, ⟨h1, h2⟩, p.y, ⟨h3, h4⟩, p.z, ⟨h5, h6⟩, hs⟩

/-- **The collision check is exact**: it reports no collision exactly when the box is free. -/
theorem collides_eq_false_iff {solid : BlockPos → Bool} {b : Box} :
    b.collides solid = false ↔ b.Free solid := by
  rw [← Bool.not_eq_true, collides_eq_true_iff]
  constructor
  · intro h p hp
    cases hs : solid p
    · rfl
    · exact absurd ⟨p, hp, hs⟩ h
  · rintro h ⟨p, hp, hs⟩
    rw [h p hp] at hs
    cases hs

end Box

namespace Vec3

theorem add_add (v : Vec3) (axis : Axis) (a b : Int) :
    (v.add axis a).add axis b = v.add axis (a + b) := by
  cases axis <;> ext <;> simp [Vec3.add] <;> omega

theorem add_zero (v : Vec3) (axis : Axis) : v.add axis 0 = v := by
  cases axis <;> ext <;> simp [Vec3.add]

theorem add_shift (pos : Vec3) (d : BlockPos) (axis : Axis) (s : Int) :
    (pos.shift d).add axis s = (pos.add axis s).shift d := by
  cases axis <;> ext <;> simp [Vec3.add, Vec3.shift] <;> omega

end Vec3

namespace Body

theorem clamp_bounds {lo hi : Int} (h : lo ≤ hi) (v : Int) :
    lo ≤ clamp lo hi v ∧ clamp lo hi v ≤ hi := by
  unfold clamp
  omega

/-- The clamped substep has the sign of the move, is at most `maxStep`, and is the whole move if that is shorter. -/
theorem clamp_step {d : Int} :
    (0 < d → 0 < clamp (-maxStep) maxStep d ∧ clamp (-maxStep) maxStep d ≤ 32768
        ∧ clamp (-maxStep) maxStep d ≤ d
        ∧ (clamp (-maxStep) maxStep d = d ∨ clamp (-maxStep) maxStep d = 32768))
      ∧ (¬ 0 < d → d ≠ 0 → clamp (-maxStep) maxStep d < 0 ∧ -32768 ≤ clamp (-maxStep) maxStep d
        ∧ d ≤ clamp (-maxStep) maxStep d
        ∧ (clamp (-maxStep) maxStep d = d ∨ clamp (-maxStep) maxStep d = -32768)) := by
  simp only [clamp, maxStep]
  omega

/-- Moving a velocity towards a target never takes it outside a range that holds both. -/
theorem approach_bounds {v target rate m : Int} (hr : 0 ≤ rate ∧ rate ≤ 16)
    (hv : -m ≤ v ∧ v ≤ m) (ht : -m ≤ target ∧ target ≤ m) :
    -m ≤ approach v target rate ∧ approach v target rate ≤ m := by
  unfold approach
  simp only []
  split
  · exact ht
  · have h1 : 0 ≤ target - v →
        0 ≤ (target - v) * rate / 16 ∧ (target - v) * rate / 16 ≤ target - v := by
      intro hg
      have : 0 ≤ (target - v) * rate := Int.mul_nonneg hg hr.1
      have : (target - v) * rate ≤ (target - v) * 16 := Int.mul_le_mul_of_nonneg_left hr.2 hg
      omega
    have h2 : target - v ≤ 0 →
        target - v ≤ (target - v) * rate / 16 ∧ (target - v) * rate / 16 ≤ 0 := by
      intro hg
      have : (target - v) * rate ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hg hr.1
      have : (target - v) * 16 ≤ (target - v) * rate := Int.mul_le_mul_of_nonpos_left hg hr.2
      omega
    omega

/-- The rounds `moveAxis` is given cover any distance up to `maxSpeed`. -/
theorem moveFuel_enough {d : Int} (hd : -maxSpeed ≤ d ∧ d ≤ maxSpeed) :
    d.natAbs ≤ 32768 * moveFuel := by
  simp only [maxSpeed, moveFuel] at hd ⊢
  omega

/-- A velocity that is within `maxSpeed` along every axis. -/
def Bounded (v : Vec3) : Prop :=
  (-maxSpeed ≤ v.x ∧ v.x ≤ maxSpeed) ∧ (-maxSpeed ≤ v.y ∧ v.y ≤ maxSpeed)
    ∧ (-maxSpeed ≤ v.z ∧ v.z ≤ maxSpeed)

instance (v : Vec3) : Decidable (Bounded v) := by
  unfold Bounded
  infer_instance

/-- The body's velocity is within `maxSpeed` along every axis. -/
def SpeedBounded (b : Body) : Prop :=
  Bounded b.vel

instance (b : Body) : Decidable b.SpeedBounded := by
  unfold SpeedBounded
  infer_instance

/-- A world's solidity, with the whole world moved by `d` blocks. -/
def shiftSolid (solid : BlockPos → Bool) (d : BlockPos) : BlockPos → Bool :=
  fun p => solid ⟨p.x - d.x, p.y - d.y, p.z - d.z⟩

/-- The body moved by a whole number of blocks. -/
def shift (b : Body) (d : BlockPos) : Body :=
  { b with pos := b.pos.shift d }

end Body

namespace Shape

open Body

theorem halfWidth_ge (sh : Shape) : 16384 ≤ sh.halfWidth := by
  have := sh.wide
  simp only [maxStep] at this
  omega

theorem height_ge (sh : Shape) : 32768 ≤ sh.height :=
  sh.tall

/-- A body standing at `pos` is not inside any solid block. -/
def Free (sh : Shape) (solid : BlockPos → Bool) (pos : Vec3) : Prop :=
  (sh.box pos).Free solid

theorem blocked_eq_false_iff {sh : Shape} {solid : BlockPos → Bool} {pos : Vec3} :
    sh.blocked solid pos = false ↔ sh.Free solid pos :=
  Box.collides_eq_false_iff

/-! ## Substeps and the paths they make -/

/-- One checked substep: a move of at most `maxStep` along one axis to a free position. -/
def SafeStep (sh : Shape) (solid : BlockPos → Bool) (a b : Vec3) : Prop :=
  ∃ axis d, b = a.add axis d ∧ -maxStep ≤ d ∧ d ≤ maxStep ∧ sh.Free solid b

/-- `b` can be reached from `a` by a chain of safe substeps. -/
inductive Reach (sh : Shape) (solid : BlockPos → Bool) : Vec3 → Vec3 → Prop
  | refl (a : Vec3) : Reach sh solid a a
  | step {a b c : Vec3} : sh.SafeStep solid a b → Reach sh solid b c → Reach sh solid a c

theorem Reach.trans {sh : Shape} {solid : BlockPos → Bool} {a b c : Vec3}
    (h₁ : sh.Reach solid a b) (h₂ : sh.Reach solid b c) : sh.Reach solid a c := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

/-- Every position on a path of safe substeps from a free position is free. -/
theorem Reach.free {sh : Shape} {solid : BlockPos → Bool} {a b : Vec3} (h : sh.Reach solid a b)
    (ha : sh.Free solid a) : sh.Free solid b := by
  induction h with
  | refl => exact ha
  | step hs _ ih =>
    obtain ⟨_, _, _, _, _, hb⟩ := hs
    exact ih hb

/--
**No tunnelling within a substep.** If both ends of a move of at most `maxStep`
along an axis are free, so is every position in between: the body's box never
leaves the union of where it started and where it ended.
-/
theorem free_between {sh : Shape} {solid : BlockPos → Bool} {a : Vec3} {axis : Axis} {d : Int}
    (ha : sh.Free solid a) (hb : sh.Free solid (a.add axis d)) (hd : -maxStep ≤ d ∧ d ≤ maxStep)
    (t : Int) (ht : (0 ≤ t ∧ t ≤ d) ∨ (d ≤ t ∧ t ≤ 0)) : sh.Free solid (a.add axis t) := by
  have hw := sh.halfWidth_ge
  have hh := sh.height_ge
  intro p hp
  by_cases h : (sh.box a).Overlaps p
  · exact ha p h
  · apply hb p
    cases axis <;>
      simp only [Box.Overlaps, box, Vec3.add, maxStep] at hp h hd ⊢ <;>
      omega

/-- The same, stated for a safe substep. -/
theorem SafeStep.free_between {sh : Shape} {solid : BlockPos → Bool} {a b : Vec3}
    (ha : sh.Free solid a) (h : sh.SafeStep solid a b) :
    ∃ axis d, b = a.add axis d ∧
      ∀ t, (0 ≤ t ∧ t ≤ d) ∨ (d ≤ t ∧ t ≤ 0) → sh.Free solid (a.add axis t) := by
  obtain ⟨axis, d, rfl, h1, h2, hb⟩ := h
  exact ⟨axis, d, rfl, Shape.free_between ha hb ⟨h1, h2⟩⟩

/-! ## Movement -/

theorem contactStep_bounds (sh : Shape) (pos : Vec3) (axis : Axis) {s : Int}
    (hs : -maxStep ≤ s ∧ s ≤ maxStep) :
    -maxStep ≤ sh.contactStep pos axis s ∧ sh.contactStep pos axis s ≤ maxStep := by
  simp only [contactStep, maxStep] at hs ⊢
  split <;> omega

/-- Wherever `moveAxis` ends up, it got there by safe substeps. -/
theorem moveAxis_reach (sh : Shape) (solid : BlockPos → Bool) (axis : Axis) (fuel : Nat)
    (pos : Vec3) (d : Int) : sh.Reach solid pos (sh.moveAxis solid axis fuel pos d).1 := by
  induction fuel generalizing pos d with
  | zero => exact .refl _
  | succ fuel ih =>
    have hs := clamp_bounds (lo := -maxStep) (hi := maxStep) (by decide) d
    simp only [moveAxis]
    split
    · exact .refl _
    · split
      · split
        · exact .refl _
        · next hnear =>
          refine .step ⟨axis, _, rfl, (sh.contactStep_bounds pos axis hs).1,
            (sh.contactStep_bounds pos axis hs).2, ?_⟩ (.refl _)
          exact blocked_eq_false_iff.mp (by simpa using hnear)
      · next hnext =>
        refine .step ⟨axis, _, rfl, hs.1, hs.2, ?_⟩ (ih _ _)
        exact blocked_eq_false_iff.mp (by simpa using hnext)

theorem move_pos (sh : Shape) (solid : BlockPos → Bool) (pos v : Vec3) :
    (sh.move solid pos v).pos =
      (sh.moveAxis solid .z moveFuel
        (sh.moveAxis solid .x moveFuel (sh.moveAxis solid .y moveFuel pos v.y).1 v.x).1 v.z).1 :=
  rfl

/-- A move takes the body along a path of safe substeps. -/
theorem move_reach (sh : Shape) (solid : BlockPos → Bool) (pos v : Vec3) :
    sh.Reach solid pos (sh.move solid pos v).pos := by
  rw [move_pos]
  exact (moveAxis_reach ..).trans ((moveAxis_reach ..).trans (moveAxis_reach ..))

/--
**No clipping.** A body that is not inside a solid block is not inside one
after a move, whatever velocity it attempts.
-/
theorem move_free {sh : Shape} {solid : BlockPos → Bool} {pos : Vec3} (v : Vec3)
    (h : sh.Free solid pos) : sh.Free solid (sh.move solid pos v).pos :=
  (sh.move_reach solid pos v).free h

/-- The body is reported as on the ground exactly when something solid is directly beneath. -/
theorem move_onGround (sh : Shape) (solid : BlockPos → Bool) (pos v : Vec3) :
    (sh.move solid pos v).onGround = sh.blocked solid ((sh.move solid pos v).pos.add .y (-1)) :=
  rfl

/-! ## Progress: movement that should happen does happen -/

/--
**An unobstructed move goes the whole way.** If every position between the
start and the intended end is free, `moveAxis` ends exactly at the intended
end and does not report a collision.
-/
theorem moveAxis_of_free {sh : Shape} {solid : BlockPos → Bool} {axis : Axis} (fuel : Nat)
    {pos : Vec3} {d : Int} (hfuel : d.natAbs ≤ 32768 * fuel)
    (hfree : ∀ t, (0 ≤ t ∧ t ≤ d) ∨ (d ≤ t ∧ t ≤ 0) → sh.Free solid (pos.add axis t)) :
    sh.moveAxis solid axis fuel pos d = (pos.add axis d, false) := by
  induction fuel generalizing pos d with
  | zero =>
    have hd : d = 0 := by omega
    subst hd
    simp [moveAxis, Vec3.add_zero]
  | succ fuel ih =>
    by_cases hd : d = 0
    · subst hd
      simp [moveAxis, Vec3.add_zero]
    · have hs : (0 ≤ clamp (-maxStep) maxStep d ∧ clamp (-maxStep) maxStep d ≤ d)
          ∨ (d ≤ clamp (-maxStep) maxStep d ∧ clamp (-maxStep) maxStep d ≤ 0) := by
        simp only [clamp, maxStep]
        omega
      have hb : sh.blocked solid (pos.add axis (clamp (-maxStep) maxStep d)) = false :=
        blocked_eq_false_iff.mpr (hfree _ hs)
      have hrest := ih (pos := pos.add axis (clamp (-maxStep) maxStep d))
        (d := d - clamp (-maxStep) maxStep d)
        (by simp only [clamp, maxStep] at hs ⊢; omega)
        (by
          intro t ht
          rw [Vec3.add_add]
          apply hfree
          simp only [clamp, maxStep] at hs ht ⊢
          omega)
      simp only [moveAxis, hd, ↓reduceIte, hb, Bool.false_eq_true, hrest, Vec3.add_add]
      congr 2
      omega

/-! ## A move goes the whole way or stops flush -/

theorem moveAxis_zero (sh : Shape) (solid : BlockPos → Bool) (axis : Axis) (fuel : Nat)
    (pos : Vec3) : sh.moveAxis solid axis fuel pos 0 = (pos, false) := by
  cases fuel <;> simp [moveAxis]

/--
Closing the gap to the next block boundary never enters a block: a free body
moved by `contactStep` is still free. So when `moveAxis` finds the way blocked,
it always takes this last short step, and its other branch is never reached.
-/
theorem contact_free {sh : Shape} {solid : BlockPos → Bool} {pos : Vec3} (axis : Axis) (s : Int)
    (hfree : sh.Free solid pos) : sh.Free solid (pos.add axis (sh.contactStep pos axis s)) := by
  intro q hq
  apply hfree q
  by_cases hs : 0 < s <;> cases axis <;>
    simp only [contactStep, hs, ↓reduceIte, Box.Overlaps, box, Vec3.add, Vec3.get] at hq ⊢ <;>
    omega

/--
**A move that is not blocked goes the whole way.** With rounds enough for the
distance, a move that reports no collision ends exactly `d` along the axis.
-/
theorem moveAxis_of_not_blocked {sh : Shape} {solid : BlockPos → Bool} {axis : Axis} (fuel : Nat)
    {pos : Vec3} {d : Int} (hfuel : d.natAbs ≤ 32768 * fuel)
    (h : (sh.moveAxis solid axis fuel pos d).2 = false) :
    (sh.moveAxis solid axis fuel pos d).1 = pos.add axis d := by
  induction fuel generalizing pos d with
  | zero =>
    have hd : d = 0 := by omega
    subst hd
    simp [moveAxis, Vec3.add_zero]
  | succ fuel ih =>
    by_cases hd : d = 0
    · subst hd
      simp [moveAxis, Vec3.add_zero]
    · have hs := @clamp_step d
      simp only [moveAxis, hd, ↓reduceIte] at h ⊢
      generalize clamp (-maxStep) maxStep d = s at hs h ⊢
      by_cases hb : sh.blocked solid (pos.add axis s) = true
      · simp only [hb, ↓reduceIte] at h
        split at h <;> cases h
      · have hb' : sh.blocked solid (pos.add axis s) = false := by simpa using hb
        simp only [hb', Bool.false_eq_true, ↓reduceIte] at h ⊢
        rw [ih (by by_cases hpos : 0 < d
                   · have := hs.1 hpos; omega
                   · have := hs.2 hpos hd; omega) h, Vec3.add_add]
        congr 1
        omega

/--
**A blocked move stops flush.** When `moveAxis` reports a collision, the body
is left touching the obstacle: one more unit the same way would be inside it.
-/
theorem moveAxis_flush {sh : Shape} {solid : BlockPos → Bool} {axis : Axis} (fuel : Nat)
    {pos : Vec3} {d : Int} (hfree : sh.Free solid pos) (hfuel : d.natAbs ≤ 32768 * fuel)
    (h : (sh.moveAxis solid axis fuel pos d).2 = true) :
    sh.blocked solid ((sh.moveAxis solid axis fuel pos d).1.add axis (if 0 < d then 1 else -1))
      = true := by
  have hw := sh.halfWidth_ge
  have hh := sh.height_ge
  induction fuel generalizing pos d with
  | zero =>
    have hd : d = 0 := by omega
    subst hd
    simp [moveAxis] at h
  | succ fuel ih =>
    by_cases hd : d = 0
    · subst hd
      simp [moveAxis] at h
    · have hs := @clamp_step d
      simp only [moveAxis, hd, ↓reduceIte] at h ⊢
      generalize clamp (-maxStep) maxStep d = s at hs h ⊢
      by_cases hb : sh.blocked solid (pos.add axis s) = true
      · have hnear : sh.blocked solid (pos.add axis (sh.contactStep pos axis s)) = false :=
          blocked_eq_false_iff.mpr (contact_free axis s hfree)
        simp only [hb, ↓reduceIte, hnear, Bool.false_eq_true] at h ⊢
        obtain ⟨q, hq, hsolid⟩ := Box.collides_eq_true_iff.mp hb
        have hnot : ¬ (sh.box pos).Overlaps q := fun ho => by
          rw [hfree q ho] at hsolid
          cases hsolid
        refine Box.collides_eq_true_iff.mpr ⟨q, ?_, hsolid⟩
        by_cases hpos : 0 < d
        · obtain ⟨h1, h2, -, -⟩ := hs.1 hpos
          cases axis <;>
            simp only [contactStep, h1, hpos, ↓reduceIte, Box.Overlaps, box, Vec3.add,
              Vec3.get] at hq hnot ⊢ <;>
            omega
        · obtain ⟨h1, h2, -, -⟩ := hs.2 hpos hd
          have h1' : ¬ 0 < s := by omega
          cases axis <;>
            simp only [contactStep, h1', hpos, ↓reduceIte, Box.Overlaps, box, Vec3.add,
              Vec3.get] at hq hnot ⊢ <;>
            omega
      · have hb' : sh.blocked solid (pos.add axis s) = false := by simpa using hb
        simp only [hb', Bool.false_eq_true, ↓reduceIte] at h ⊢
        by_cases hrest : d - s = 0
        · rw [hrest, moveAxis_zero] at h
          cases h
        · have hsign : (if 0 < d - s then (1 : Int) else -1) = (if 0 < d then 1 else -1) := by
            by_cases hpos : 0 < d
            · have := hs.1 hpos
              have hc : 0 < d - s := by omega
              simp only [hpos, hc, ↓reduceIte]
            · have := hs.2 hpos hd
              have hc : ¬ 0 < d - s := by omega
              simp only [hpos, hc, ↓reduceIte]
          have := ih (blocked_eq_false_iff.mp hb')
            (by by_cases hpos : 0 < d
                · have := hs.1 hpos; omega
                · have := hs.2 hpos hd; omega) h
          rw [hsign] at this
          exact this

/-! ## Speed -/

/-- **Speed is bounded.** A move never leaves a body faster along any axis than it set out. -/
theorem move_speedBounded (sh : Shape) (solid : BlockPos → Bool) (pos : Vec3) {v : Vec3}
    (h : Bounded v) : (sh.move solid pos v).SpeedBounded := by
  obtain ⟨hx, hy, hz⟩ := h
  simp only [SpeedBounded, Bounded, move, maxSpeed] at hx hy hz ⊢
  refine ⟨?_, ?_, ?_⟩ <;> split <;> omega

/--
**Blocked means an obstacle.** In the game, where no axis is ever asked to move
further than `maxSpeed`, a move reported as blocked has stopped flush against
something solid; it has not merely run out of rounds.
-/
theorem moveAxis_flush_of_speed {sh : Shape} {solid : BlockPos → Bool} {axis : Axis} {pos : Vec3}
    {d : Int} (hfree : sh.Free solid pos) (hd : -maxSpeed ≤ d ∧ d ≤ maxSpeed)
    (h : (sh.moveAxis solid axis moveFuel pos d).2 = true) :
    sh.blocked solid ((sh.moveAxis solid axis moveFuel pos d).1.add axis (if 0 < d then 1 else -1))
      = true :=
  moveAxis_flush moveFuel hfree (moveFuel_enough hd) h

/-- And one not reported as blocked has gone the whole way. -/
theorem moveAxis_of_not_blocked_of_speed {sh : Shape} {solid : BlockPos → Bool} {axis : Axis}
    {pos : Vec3} {d : Int} (hd : -maxSpeed ≤ d ∧ d ≤ maxSpeed)
    (h : (sh.moveAxis solid axis moveFuel pos d).2 = false) :
    (sh.moveAxis solid axis moveFuel pos d).1 = pos.add axis d :=
  moveAxis_of_not_blocked moveFuel (moveFuel_enough hd) h

/-! ## The floor -/

theorem SafeStep.above_floor {sh : Shape} {solid : BlockPos → Bool} {a b : Vec3}
    (hfloor : ∀ x z, solid ⟨x, 0, z⟩ = true) (ha : 65536 ≤ a.y) (h : sh.SafeStep solid a b) :
    65536 ≤ b.y := by
  have hw := sh.halfWidth_ge
  have hh := sh.height_ge
  obtain ⟨axis, d, rfl, h1, h2, hb⟩ := h
  apply Classical.byContradiction
  intro hlt
  have hov : (sh.box (a.add axis d)).Overlaps
      ⟨(a.add axis d).x / 65536, 0, (a.add axis d).z / 65536⟩ := by
    cases axis <;>
      simp only [Box.Overlaps, box, Vec3.add, maxStep] at h1 h2 hlt ⊢ <;>
      omega
  have := hb _ hov
  rw [hfloor] at this
  cases this

theorem Reach.above_floor {sh : Shape} {solid : BlockPos → Bool} {a b : Vec3}
    (hfloor : ∀ x z, solid ⟨x, 0, z⟩ = true) (h : sh.Reach solid a b) (ha : 65536 ≤ a.y) :
    65536 ≤ b.y := by
  induction h with
  | refl => exact ha
  | step hs _ ih => exact ih (hs.above_floor hfloor ha)

/--
**The floor holds.** If the whole layer at height zero is solid, a body whose
feet are above it never ends a move with its feet below its top.
-/
theorem move_above_floor {sh : Shape} {solid : BlockPos → Bool}
    (hfloor : ∀ x z, solid ⟨x, 0, z⟩ = true) {pos : Vec3} (v : Vec3) (h : 65536 ≤ pos.y) :
    65536 ≤ (sh.move solid pos v).pos.y :=
  (sh.move_reach solid pos v).above_floor hfloor h

/-! ## Settling a new body -/

theorem settle_free {sh : Shape} {solid : BlockPos → Bool} (drop : Nat) {pos : Vec3}
    (h : sh.Free solid pos) : sh.Free solid (sh.settle solid drop pos) := by
  induction drop generalizing pos with
  | zero => exact h
  | succ drop ih =>
    simp only [settle]
    split
    · exact h
    · next hb => exact ih (blocked_eq_false_iff.mp (by simpa using hb))

/-- Settling only lowers: it moves a position neither along `x` nor along `z`. -/
theorem settle_xz (sh : Shape) (solid : BlockPos → Bool) (drop : Nat) (pos : Vec3) :
    (sh.settle solid drop pos).x = pos.x ∧ (sh.settle solid drop pos).z = pos.z := by
  induction drop generalizing pos with
  | zero => exact ⟨rfl, rfl⟩
  | succ drop ih =>
    simp only [settle]
    split
    · exact ⟨rfl, rfl⟩
    · exact ih _

/-- Settling from a whole-block height above a solid floor stops above the floor. -/
theorem settle_above_floor {sh : Shape} {solid : BlockPos → Bool}
    (hfloor : ∀ x z, solid ⟨x, 0, z⟩ = true) (drop : Nat) {pos : Vec3} (h : 65536 ≤ pos.y)
    (hm : pos.y % 65536 = 0) : 65536 ≤ (sh.settle solid drop pos).y := by
  have hw := sh.halfWidth_ge
  have hh := sh.height_ge
  induction drop generalizing pos with
  | zero => exact h
  | succ drop ih =>
    simp only [settle]
    split
    · exact h
    · next hb =>
      have hfree : sh.Free solid (pos.add .y (-65536)) :=
        blocked_eq_false_iff.mp (by simpa using hb)
      have hy : (pos.add .y (-65536)).y = pos.y - 65536 := by simp [Vec3.add]; omega
      refine ih ?_ (by omega)
      apply Classical.byContradiction
      intro hlt
      have hov : (sh.box (pos.add .y (-65536))).Overlaps
          ⟨(pos.add .y (-65536)).x / 65536, 0, (pos.add .y (-65536)).z / 65536⟩ := by
        simp only [Box.Overlaps, box, Vec3.add] at hy hlt ⊢
        omega
      have := hfree _ hov
      rw [hfloor] at this
      cases this

/-- A free body at a whole-block height with something a block below is standing on it. -/
theorem blocked_below_of_block_below {sh : Shape} {solid : BlockPos → Bool} {pos : Vec3}
    (hfree : sh.Free solid pos) (hm : pos.y % 65536 = 0)
    (h : sh.blocked solid (pos.add .y (-65536)) = true) :
    sh.blocked solid (pos.add .y (-1)) = true := by
  have hh := sh.height_ge
  obtain ⟨q, hq, hsolid⟩ := Box.collides_eq_true_iff.mp h
  have hnot : ¬ (sh.box pos).Overlaps q := fun ho => by
    rw [hfree q ho] at hsolid
    cases hsolid
  refine Box.collides_eq_true_iff.mpr ⟨q, ?_, hsolid⟩
  simp only [Box.Overlaps, box, Vec3.add] at hq hnot ⊢
  omega

/--
Settling from a whole-block height ends on the ground, if there is ground to
be found within the drop: the body comes to rest with something solid directly
beneath.
-/
theorem settle_grounded {sh : Shape} {solid : BlockPos → Bool} (drop : Nat) {pos : Vec3}
    (hfree : sh.Free solid pos) (hm : pos.y % 65536 = 0)
    (hbelow : ∃ k : Nat, k ≤ drop ∧ sh.blocked solid (pos.add .y (-(65536 * (k + 1)))) = true) :
    sh.blocked solid ((sh.settle solid drop pos).add .y (-1)) = true := by
  induction drop generalizing pos with
  | zero =>
    obtain ⟨k, hk, hb⟩ := hbelow
    have : k = 0 := by omega
    subst this
    exact blocked_below_of_block_below hfree hm hb
  | succ drop ih =>
    simp only [settle]
    split
    · next hb => exact blocked_below_of_block_below hfree hm hb
    · next hb =>
      obtain ⟨k, hk, hbk⟩ := hbelow
      cases k with
      | zero => exact absurd hbk hb
      | succ k =>
        refine ih (blocked_eq_false_iff.mp (by simpa using hb))
          (by simp only [Vec3.add]; omega) ⟨k, by omega, ?_⟩
        rw [Vec3.add_add]
        have : (-65536 : Int) + -(65536 * ((k : Int) + 1))
            = -(65536 * (((k + 1 : Nat) : Int) + 1)) := by
          omega
        rw [this]
        exact hbk

/-! ## Translation invariance -/

theorem blocked_shift (sh : Shape) (solid : BlockPos → Bool) (d : BlockPos) (pos : Vec3) :
    sh.blocked (shiftSolid solid d) (pos.shift d) = sh.blocked solid pos := by
  rw [Bool.eq_iff_iff]
  unfold blocked
  rw [Box.collides_eq_true_iff, Box.collides_eq_true_iff]
  constructor
  · rintro ⟨p, hp, hs⟩
    refine ⟨⟨p.x - d.x, p.y - d.y, p.z - d.z⟩, ?_, hs⟩
    simp only [Box.Overlaps, box, Vec3.shift] at hp ⊢
    omega
  · rintro ⟨q, hq, hs⟩
    refine ⟨⟨q.x + d.x, q.y + d.y, q.z + d.z⟩, ?_, ?_⟩
    · simp only [Box.Overlaps, box, Vec3.shift] at hq ⊢
      omega
    · have : (⟨q.x + d.x - d.x, q.y + d.y - d.y, q.z + d.z - d.z⟩ : BlockPos) = q := by
        ext <;> simp
      simp only [shiftSolid, this, hs]

theorem contactStep_shift (sh : Shape) (pos : Vec3) (d : BlockPos) (axis : Axis) (s : Int) :
    sh.contactStep (pos.shift d) axis s = sh.contactStep pos axis s := by
  by_cases h : 0 < s <;> cases axis <;>
    simp only [contactStep, h, ↓reduceIte, box, Vec3.get, Vec3.shift] <;>
    omega

theorem moveAxis_shift (sh : Shape) (solid : BlockPos → Bool) (d : BlockPos) (axis : Axis)
    (fuel : Nat) (pos : Vec3) (dist : Int) :
    sh.moveAxis (shiftSolid solid d) axis fuel (pos.shift d) dist =
      ((sh.moveAxis solid axis fuel pos dist).1.shift d,
        (sh.moveAxis solid axis fuel pos dist).2) := by
  induction fuel generalizing pos dist with
  | zero => rfl
  | succ fuel ih =>
    simp only [moveAxis, Vec3.add_shift, blocked_shift, contactStep_shift, ih]
    repeat' split
    all_goals rfl

/--
**Physics is the same everywhere.** Moving the world and the body by any whole
number of blocks and then moving gives the same result as moving first.
-/
theorem move_shift (sh : Shape) (solid : BlockPos → Bool) (d : BlockPos) (pos v : Vec3) :
    sh.move (shiftSolid solid d) (pos.shift d) v = (sh.move solid pos v).shift d := by
  simp only [move, Body.shift, moveAxis_shift, Vec3.add_shift, blocked_shift]

end Shape

end LeanMc
