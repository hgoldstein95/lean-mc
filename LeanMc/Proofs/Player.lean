import LeanMc.Core.Player

/-!
# Player physics theorems

* **The collision check is exact.** `Box.collides` is false exactly when no
  solid block overlaps the box.
* **No clipping.** A player who is not inside a solid block is still not inside
  one after a tick, whatever the input.
* **No tunnelling.** A tick moves the player through a chain of short,
  axis-aligned substeps, and the player's box is clear of solid blocks at every
  point along every substep, not only at its ends.
* **A move goes the whole way or stops flush.** A move that is not reported as
  blocked ends exactly where it was meant to; one that is leaves the player
  touching what stopped it, with no gap. So "blocked" always means an obstacle.
* **Speed is bounded.** No axis of the velocity ever exceeds `maxSpeed`, so the
  rounds `moveAxis` is given always suffice.
* **The floor holds.** Over a solid floor at height zero, the player's feet
  never go below the top of that floor.
* **Physics is the same everywhere.** Shifting the world and the player by any
  whole number of blocks commutes with a tick. This is false for floating
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

namespace Player

/-- A player standing at `pos` is not inside any solid block. -/
def Free (solid : BlockPos → Bool) (pos : Vec3) : Prop :=
  (box pos).Free solid

theorem blocked_eq_false_iff {solid : BlockPos → Bool} {pos : Vec3} :
    blocked solid pos = false ↔ Free solid pos :=
  Box.collides_eq_false_iff

/-! ## Substeps and the paths they make -/

/-- One checked substep: a move of at most `maxStep` along one axis to a free position. -/
def SafeStep (solid : BlockPos → Bool) (a b : Vec3) : Prop :=
  ∃ axis d, b = a.add axis d ∧ -maxStep ≤ d ∧ d ≤ maxStep ∧ Free solid b

/-- `b` can be reached from `a` by a chain of safe substeps. -/
inductive Reach (solid : BlockPos → Bool) : Vec3 → Vec3 → Prop
  | refl (a : Vec3) : Reach solid a a
  | step {a b c : Vec3} : SafeStep solid a b → Reach solid b c → Reach solid a c

theorem Reach.trans {solid : BlockPos → Bool} {a b c : Vec3} (h₁ : Reach solid a b)
    (h₂ : Reach solid b c) : Reach solid a c := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

/-- Every position on a path of safe substeps from a free position is free. -/
theorem Reach.free {solid : BlockPos → Bool} {a b : Vec3} (h : Reach solid a b)
    (ha : Free solid a) : Free solid b := by
  induction h with
  | refl => exact ha
  | step hs _ ih =>
    obtain ⟨_, _, _, _, _, hb⟩ := hs
    exact ih hb

/--
**No tunnelling within a substep.** If both ends of a move of at most `maxStep`
along an axis are free, so is every position in between: the player's box
never leaves the union of where it started and where it ended.
-/
theorem free_between {solid : BlockPos → Bool} {a : Vec3} {axis : Axis} {d : Int}
    (ha : Free solid a) (hb : Free solid (a.add axis d)) (hd : -maxStep ≤ d ∧ d ≤ maxStep)
    (t : Int) (ht : (0 ≤ t ∧ t ≤ d) ∨ (d ≤ t ∧ t ≤ 0)) : Free solid (a.add axis t) := by
  intro p hp
  by_cases h : (box a).Overlaps p
  · exact ha p h
  · apply hb p
    cases axis <;>
      simp only [Box.Overlaps, box, Vec3.add, halfWidth, height, maxStep] at hp h hd ⊢ <;>
      omega

/-- The same, stated for a safe substep. -/
theorem SafeStep.free_between {solid : BlockPos → Bool} {a b : Vec3} (ha : Free solid a)
    (h : SafeStep solid a b) :
    ∃ axis d, b = a.add axis d ∧
      ∀ t, (0 ≤ t ∧ t ≤ d) ∨ (d ≤ t ∧ t ≤ 0) → Free solid (a.add axis t) := by
  obtain ⟨axis, d, rfl, h1, h2, hb⟩ := h
  exact ⟨axis, d, rfl, Player.free_between ha hb ⟨h1, h2⟩⟩

/-! ## Movement -/

theorem clamp_bounds {lo hi : Int} (h : lo ≤ hi) (v : Int) :
    lo ≤ clamp lo hi v ∧ clamp lo hi v ≤ hi := by
  unfold clamp
  omega

theorem contactStep_bounds (pos : Vec3) (axis : Axis) {s : Int}
    (hs : -maxStep ≤ s ∧ s ≤ maxStep) :
    -maxStep ≤ contactStep pos axis s ∧ contactStep pos axis s ≤ maxStep := by
  simp only [contactStep, maxStep] at hs ⊢
  split <;> omega

/-- Wherever `moveAxis` ends up, it got there by safe substeps. -/
theorem moveAxis_reach (solid : BlockPos → Bool) (axis : Axis) (fuel : Nat) (pos : Vec3)
    (d : Int) : Reach solid pos (moveAxis solid axis fuel pos d).1 := by
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
          refine .step ⟨axis, _, rfl, (contactStep_bounds pos axis hs).1,
            (contactStep_bounds pos axis hs).2, ?_⟩ (.refl _)
          exact blocked_eq_false_iff.mp (by simpa using hnear)
      · next hnext =>
        refine .step ⟨axis, _, rfl, hs.1, hs.2, ?_⟩ (ih _ _)
        exact blocked_eq_false_iff.mp (by simpa using hnext)

theorem step_pos (solid : BlockPos → Bool) (input : Input) (p : Player) :
    (step solid input p).pos =
      (moveAxis solid .z moveFuel
        (moveAxis solid .x moveFuel
          (moveAxis solid .y moveFuel p.pos (intent input p).y).1 (intent input p).x).1
        (intent input p).z).1 := rfl

/-- A tick moves the player along a path of safe substeps. -/
theorem step_reach (solid : BlockPos → Bool) (input : Input) (p : Player) :
    Reach solid p.pos (step solid input p).pos := by
  rw [step_pos]
  exact (moveAxis_reach ..).trans ((moveAxis_reach ..).trans (moveAxis_reach ..))

/--
**No clipping.** A player who is not inside a solid block is not inside one
after a tick, whatever the input and however fast they were moving.
-/
theorem step_free {solid : BlockPos → Bool} (input : Input) {p : Player}
    (h : Free solid p.pos) : Free solid (step solid input p).pos :=
  (step_reach solid input p).free h

/-- The player is reported as on the ground exactly when something solid is directly beneath. -/
theorem step_onGround (solid : BlockPos → Bool) (input : Input) (p : Player) :
    (step solid input p).onGround = false ↔
      Free solid ((step solid input p).pos.add .y (-1)) :=
  blocked_eq_false_iff

/-! ## Progress: movement that should happen does happen -/

theorem add_add (v : Vec3) (axis : Axis) (a b : Int) :
    (v.add axis a).add axis b = v.add axis (a + b) := by
  cases axis <;> ext <;> simp [Vec3.add] <;> omega

theorem add_zero (v : Vec3) (axis : Axis) : v.add axis 0 = v := by
  cases axis <;> ext <;> simp [Vec3.add]

/--
**An unobstructed move goes the whole way.** If every position between the
start and the intended end is free, `moveAxis` ends exactly at the intended
end and does not report a collision.
-/
theorem moveAxis_of_free {solid : BlockPos → Bool} {axis : Axis} (fuel : Nat) {pos : Vec3}
    {d : Int} (hfuel : d.natAbs ≤ 32768 * fuel)
    (hfree : ∀ t, (0 ≤ t ∧ t ≤ d) ∨ (d ≤ t ∧ t ≤ 0) → Free solid (pos.add axis t)) :
    moveAxis solid axis fuel pos d = (pos.add axis d, false) := by
  induction fuel generalizing pos d with
  | zero =>
    have hd : d = 0 := by omega
    subst hd
    simp [moveAxis, add_zero]
  | succ fuel ih =>
    by_cases hd : d = 0
    · subst hd
      simp [moveAxis, add_zero]
    · have hs : (0 ≤ clamp (-maxStep) maxStep d ∧ clamp (-maxStep) maxStep d ≤ d)
          ∨ (d ≤ clamp (-maxStep) maxStep d ∧ clamp (-maxStep) maxStep d ≤ 0) := by
        simp only [clamp, maxStep]
        omega
      have hb : blocked solid (pos.add axis (clamp (-maxStep) maxStep d)) = false :=
        blocked_eq_false_iff.mpr (hfree _ hs)
      have hrest := ih (pos := pos.add axis (clamp (-maxStep) maxStep d))
        (d := d - clamp (-maxStep) maxStep d)
        (by simp only [clamp, maxStep] at hs ⊢; omega)
        (by
          intro t ht
          rw [add_add]
          apply hfree
          simp only [clamp, maxStep] at hs ht ⊢
          omega)
      simp only [moveAxis, hd, ↓reduceIte, hb, Bool.false_eq_true, hrest, add_add]
      congr 2
      omega

/--
**Standing still is still.** A player at rest on something solid, asking for
nothing, is in exactly the same place after a tick, with no drift or jitter.
-/
theorem step_rest {solid : BlockPos → Bool} {p : Player} (hfree : Free solid p.pos)
    (hground : blocked solid (p.pos.add .y (-1)) = true) (hvel : p.vel = ⟨0, 0, 0⟩)
    (hfly : p.flying = false) :
    (step solid {} p).pos = p.pos ∧ (step solid {} p).vel = ⟨0, 0, 0⟩ := by
  -- What is underfoot touches the player's feet exactly.
  obtain ⟨q, hq, hsolid⟩ := Box.collides_eq_true_iff.mp hground
  have hnot : ¬ (box p.pos).Overlaps q := fun h => by
    rw [hfree q h] at hsolid
    cases hsolid
  have hfeet : p.pos.y = (q.y + 1) * 65536 := by
    simp only [Box.Overlaps, box, Vec3.add, halfWidth, height] at hq hnot
    omega
  -- So falling is blocked at once, and the gap to close is zero.
  have hintent : intent {} p = ⟨0, -583, 0⟩ := by
    have h0 : clamp (-maxSpeed) maxSpeed 0 = 0 := by decide
    have ha : ∀ r, approach 0 0 r = 0 := fun r => by simp [approach]
    have hg : max (-maxSpeed) (0 - gravity) = -583 := by decide
    simp only [intent, hvel, hfly, h0, ha, hg, Bool.false_bne,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  have hfall : blocked solid (p.pos.add .y (-583)) = true := by
    refine Box.collides_eq_true_iff.mpr ⟨q, ?_, hsolid⟩
    simp only [Box.Overlaps, box, Vec3.add, halfWidth, height] at hq ⊢
    omega
  have hcontact : contactStep p.pos .y (-583) = 0 := by
    simp only [contactStep, box, Vec3.get, hfeet]
    omega
  have hy : moveAxis solid .y moveFuel p.pos (-583) = (p.pos, true) := by
    have hclamp : clamp (-maxStep) maxStep (-583) = -583 := by decide
    have hstay : blocked solid p.pos = false := blocked_eq_false_iff.mpr hfree
    simp [moveAxis, moveFuel, hclamp, hfall, hcontact, add_zero, hstay]
  have hx : ∀ axis, moveAxis solid axis moveFuel p.pos 0 = (p.pos, false) := fun axis => by
    simp [moveAxis, moveFuel]
  simp [step, hintent, hy, hx]

/-! ## A move goes the whole way or stops flush -/

theorem moveAxis_zero (solid : BlockPos → Bool) (axis : Axis) (fuel : Nat) (pos : Vec3) :
    moveAxis solid axis fuel pos 0 = (pos, false) := by
  cases fuel <;> simp [moveAxis]

/--
Closing the gap to the next block boundary never enters a block: a free player
moved by `contactStep` is still free. So when `moveAxis` finds the way blocked,
it always takes this last short step, and its other branch is never reached.
-/
theorem contact_free {solid : BlockPos → Bool} {pos : Vec3} (axis : Axis) (s : Int)
    (hfree : Free solid pos) : Free solid (pos.add axis (contactStep pos axis s)) := by
  intro q hq
  apply hfree q
  by_cases hs : 0 < s <;> cases axis <;>
    simp only [contactStep, hs, ↓reduceIte, Box.Overlaps, box, Vec3.add, Vec3.get, halfWidth,
      height] at hq ⊢ <;>
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

/--
**A move that is not blocked goes the whole way.** With rounds enough for the
distance, a move that reports no collision ends exactly `d` along the axis.
-/
theorem moveAxis_of_not_blocked {solid : BlockPos → Bool} {axis : Axis} (fuel : Nat) {pos : Vec3}
    {d : Int} (hfuel : d.natAbs ≤ 32768 * fuel)
    (h : (moveAxis solid axis fuel pos d).2 = false) :
    (moveAxis solid axis fuel pos d).1 = pos.add axis d := by
  induction fuel generalizing pos d with
  | zero =>
    have hd : d = 0 := by omega
    subst hd
    simp [moveAxis, add_zero]
  | succ fuel ih =>
    by_cases hd : d = 0
    · subst hd
      simp [moveAxis, add_zero]
    · have hs := @clamp_step d
      simp only [moveAxis, hd, ↓reduceIte] at h ⊢
      generalize clamp (-maxStep) maxStep d = s at hs h ⊢
      by_cases hb : blocked solid (pos.add axis s) = true
      · simp only [hb, ↓reduceIte] at h
        split at h <;> cases h
      · have hb' : blocked solid (pos.add axis s) = false := by simpa using hb
        simp only [hb', Bool.false_eq_true, ↓reduceIte] at h ⊢
        rw [ih (by by_cases hpos : 0 < d
                   · have := hs.1 hpos; omega
                   · have := hs.2 hpos hd; omega) h, add_add]
        congr 1
        omega

/--
**A blocked move stops flush.** When `moveAxis` reports a collision, the player
is left touching the obstacle: one more unit the same way would be inside it.
-/
theorem moveAxis_flush {solid : BlockPos → Bool} {axis : Axis} (fuel : Nat) {pos : Vec3} {d : Int}
    (hfree : Free solid pos) (hfuel : d.natAbs ≤ 32768 * fuel)
    (h : (moveAxis solid axis fuel pos d).2 = true) :
    blocked solid ((moveAxis solid axis fuel pos d).1.add axis (if 0 < d then 1 else -1)) = true := by
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
      by_cases hb : blocked solid (pos.add axis s) = true
      · have hnear : blocked solid (pos.add axis (contactStep pos axis s)) = false :=
          blocked_eq_false_iff.mpr (contact_free axis s hfree)
        simp only [hb, ↓reduceIte, hnear, Bool.false_eq_true] at h ⊢
        obtain ⟨q, hq, hsolid⟩ := Box.collides_eq_true_iff.mp hb
        have hnot : ¬ (box pos).Overlaps q := fun ho => by
          rw [hfree q ho] at hsolid
          cases hsolid
        refine Box.collides_eq_true_iff.mpr ⟨q, ?_, hsolid⟩
        by_cases hpos : 0 < d
        · obtain ⟨h1, h2, -, -⟩ := hs.1 hpos
          cases axis <;>
            simp only [contactStep, h1, hpos, ↓reduceIte, Box.Overlaps, box, Vec3.add, Vec3.get,
              halfWidth, height] at hq hnot ⊢ <;>
            omega
        · obtain ⟨h1, h2, -, -⟩ := hs.2 hpos hd
          have h1' : ¬ 0 < s := by omega
          cases axis <;>
            simp only [contactStep, h1', hpos, ↓reduceIte, Box.Overlaps, box, Vec3.add, Vec3.get,
              halfWidth, height] at hq hnot ⊢ <;>
            omega
      · have hb' : blocked solid (pos.add axis s) = false := by simpa using hb
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

/-- The velocity is within `maxSpeed` along every axis. -/
def SpeedBounded (p : Player) : Prop :=
  (-maxSpeed ≤ p.vel.x ∧ p.vel.x ≤ maxSpeed) ∧ (-maxSpeed ≤ p.vel.y ∧ p.vel.y ≤ maxSpeed)
    ∧ (-maxSpeed ≤ p.vel.z ∧ p.vel.z ≤ maxSpeed)

instance (p : Player) : Decidable p.SpeedBounded := by
  unfold SpeedBounded
  infer_instance

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

/-- What the player attempts in a tick is within `maxSpeed` along every axis. -/
theorem intent_bounds (input : Input) {p : Player} (h : p.SpeedBounded) :
    (-maxSpeed ≤ (intent input p).x ∧ (intent input p).x ≤ maxSpeed)
      ∧ (-maxSpeed ≤ (intent input p).y ∧ (intent input p).y ≤ maxSpeed)
      ∧ (-maxSpeed ≤ (intent input p).z ∧ (intent input p).z ≤ maxSpeed) := by
  obtain ⟨hx, hy, hz⟩ := h
  have hr : ∀ b : Bool, (0 : Int) ≤ (if b then 8 else 2) ∧ (if b then 8 else 2 : Int) ≤ 16 := by
    intro b; cases b <;> decide
  have cx := clamp_bounds (lo := -maxSpeed) (hi := maxSpeed) (by decide) input.wishX
  have cz := clamp_bounds (lo := -maxSpeed) (hi := maxSpeed) (by decide) input.wishZ
  refine ⟨approach_bounds (hr _) hx cx, ?_, approach_bounds (hr _) hz cz⟩
  simp only [intent, maxSpeed, flySpeed, jumpSpeed, gravity] at hy ⊢
  repeat' split
  all_goals omega

/-- **Speed is bounded.** A tick never leaves the player faster than `maxSpeed` along any axis. -/
theorem step_speedBounded (solid : BlockPos → Bool) (input : Input) {p : Player}
    (h : p.SpeedBounded) : (step solid input p).SpeedBounded := by
  obtain ⟨hx, hy, hz⟩ := intent_bounds input h
  simp only [SpeedBounded, step, maxSpeed] at hx hy hz ⊢
  refine ⟨?_, ?_, ?_⟩ <;> split <;> omega

/-- The rounds `moveAxis` is given cover any distance up to `maxSpeed`. -/
theorem moveFuel_enough {d : Int} (hd : -maxSpeed ≤ d ∧ d ≤ maxSpeed) :
    d.natAbs ≤ 32768 * moveFuel := by
  simp only [maxSpeed, moveFuel] at hd ⊢
  omega

/--
**Blocked means an obstacle.** In the game, where no axis is ever asked to move
further than `maxSpeed`, a move reported as blocked has stopped flush against
something solid; it has not merely run out of rounds.
-/
theorem moveAxis_flush_of_speed {solid : BlockPos → Bool} {axis : Axis} {pos : Vec3} {d : Int}
    (hfree : Free solid pos) (hd : -maxSpeed ≤ d ∧ d ≤ maxSpeed)
    (h : (moveAxis solid axis moveFuel pos d).2 = true) :
    blocked solid ((moveAxis solid axis moveFuel pos d).1.add axis (if 0 < d then 1 else -1))
      = true :=
  moveAxis_flush moveFuel hfree (moveFuel_enough hd) h

/-- And one not reported as blocked has gone the whole way. -/
theorem moveAxis_of_not_blocked_of_speed {solid : BlockPos → Bool} {axis : Axis} {pos : Vec3}
    {d : Int} (hd : -maxSpeed ≤ d ∧ d ≤ maxSpeed)
    (h : (moveAxis solid axis moveFuel pos d).2 = false) :
    (moveAxis solid axis moveFuel pos d).1 = pos.add axis d :=
  moveAxis_of_not_blocked moveFuel (moveFuel_enough hd) h

/--
**No jumping in mid-air.** A player who is not flying and has nothing beneath
them can only fall: the vertical speed they attempt is the old one less
gravity, down to the fastest fall.
-/
theorem intent_airborne (input : Input) {p : Player} (hair : p.onGround = false)
    (hfly : (p.flying != input.toggleFly) = false) :
    (intent input p).y = max (-maxSpeed) (p.vel.y - gravity) := by
  simp [intent, hair, hfly]

/-! ## The floor -/

theorem SafeStep.above_floor {solid : BlockPos → Bool} {a b : Vec3}
    (hfloor : ∀ x z, solid ⟨x, 0, z⟩ = true) (ha : 65536 ≤ a.y) (h : SafeStep solid a b) :
    65536 ≤ b.y := by
  obtain ⟨axis, d, rfl, h1, h2, hb⟩ := h
  apply Classical.byContradiction
  intro hlt
  have hov : (box (a.add axis d)).Overlaps ⟨(a.add axis d).x / 65536, 0, (a.add axis d).z / 65536⟩ := by
    cases axis <;>
      simp only [Box.Overlaps, box, Vec3.add, halfWidth, height, maxStep] at h1 h2 hlt ⊢ <;>
      omega
  have := hb _ hov
  rw [hfloor] at this
  cases this

theorem Reach.above_floor {solid : BlockPos → Bool} {a b : Vec3}
    (hfloor : ∀ x z, solid ⟨x, 0, z⟩ = true) (h : Reach solid a b) (ha : 65536 ≤ a.y) :
    65536 ≤ b.y := by
  induction h with
  | refl => exact ha
  | step hs _ ih => exact ih (hs.above_floor hfloor ha)

/--
**The floor holds.** If the whole layer at height zero is solid, a player whose
feet are above it never ends a tick with their feet below its top.
-/
theorem step_above_floor {solid : BlockPos → Bool} (hfloor : ∀ x z, solid ⟨x, 0, z⟩ = true)
    (input : Input) {p : Player} (h : 65536 ≤ p.pos.y) : 65536 ≤ (step solid input p).pos.y :=
  (step_reach solid input p).above_floor hfloor h

/-! ## Settling a new player -/

theorem settle_free {solid : BlockPos → Bool} (drop : Nat) {pos : Vec3} (h : Free solid pos) :
    Free solid (settle solid drop pos) := by
  induction drop generalizing pos with
  | zero => exact h
  | succ drop ih =>
    simp only [settle]
    split
    · exact h
    · next hb => exact ih (blocked_eq_false_iff.mp (by simpa using hb))

/-- Settling from a whole-block height above a solid floor stops above the floor. -/
theorem settle_above_floor {solid : BlockPos → Bool} (hfloor : ∀ x z, solid ⟨x, 0, z⟩ = true)
    (drop : Nat) {pos : Vec3} (h : 65536 ≤ pos.y) (hm : pos.y % 65536 = 0) :
    65536 ≤ (settle solid drop pos).y := by
  induction drop generalizing pos with
  | zero => exact h
  | succ drop ih =>
    simp only [settle]
    split
    · exact h
    · next hb =>
      have hfree : Free solid (pos.add .y (-65536)) := blocked_eq_false_iff.mp (by simpa using hb)
      have hy : (pos.add .y (-65536)).y = pos.y - 65536 := by simp [Vec3.add]; omega
      refine ih ?_ (by omega)
      apply Classical.byContradiction
      intro hlt
      have hov : (box (pos.add .y (-65536))).Overlaps
          ⟨(pos.add .y (-65536)).x / 65536, 0, (pos.add .y (-65536)).z / 65536⟩ := by
        simp only [Box.Overlaps, box, Vec3.add, halfWidth, height] at hy hlt ⊢
        omega
      have := hfree _ hov
      rw [hfloor] at this
      cases this

/-- A free player at a whole-block height with something a block below is standing on it. -/
theorem blocked_below_of_block_below {solid : BlockPos → Bool} {pos : Vec3} (hfree : Free solid pos)
    (hm : pos.y % 65536 = 0) (h : blocked solid (pos.add .y (-65536)) = true) :
    blocked solid (pos.add .y (-1)) = true := by
  obtain ⟨q, hq, hsolid⟩ := Box.collides_eq_true_iff.mp h
  have hnot : ¬ (box pos).Overlaps q := fun ho => by
    rw [hfree q ho] at hsolid
    cases hsolid
  refine Box.collides_eq_true_iff.mpr ⟨q, ?_, hsolid⟩
  simp only [Box.Overlaps, box, Vec3.add, halfWidth, height] at hq hnot ⊢
  omega

/--
Settling from a whole-block height ends on the ground, if there is ground to
be found within the drop: the player comes to rest with something solid
directly beneath.
-/
theorem settle_grounded {solid : BlockPos → Bool} (drop : Nat) {pos : Vec3} (hfree : Free solid pos)
    (hm : pos.y % 65536 = 0)
    (hbelow : ∃ k : Nat, k ≤ drop ∧ blocked solid (pos.add .y (-(65536 * (k + 1)))) = true) :
    blocked solid ((settle solid drop pos).add .y (-1)) = true := by
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
        rw [add_add]
        have : (-65536 : Int) + -(65536 * ((k : Int) + 1)) = -(65536 * (((k + 1 : Nat) : Int) + 1)) := by
          omega
        rw [this]
        exact hbk

/-! ## Translation invariance -/

/-- The player moved by a whole number of blocks. -/
def shift (p : Player) (d : BlockPos) : Player :=
  { p with pos := p.pos.shift d }

/-- A world's solidity, with the whole world moved by `d` blocks. -/
def shiftSolid (solid : BlockPos → Bool) (d : BlockPos) : BlockPos → Bool :=
  fun p => solid ⟨p.x - d.x, p.y - d.y, p.z - d.z⟩

theorem add_shift (pos : Vec3) (d : BlockPos) (axis : Axis) (s : Int) :
    (pos.shift d).add axis s = (pos.add axis s).shift d := by
  cases axis <;> ext <;> simp [Vec3.add, Vec3.shift] <;> omega

theorem blocked_shift (solid : BlockPos → Bool) (d : BlockPos) (pos : Vec3) :
    blocked (shiftSolid solid d) (pos.shift d) = blocked solid pos := by
  rw [Bool.eq_iff_iff]
  unfold blocked
  rw [Box.collides_eq_true_iff, Box.collides_eq_true_iff]
  constructor
  · rintro ⟨p, hp, hs⟩
    refine ⟨⟨p.x - d.x, p.y - d.y, p.z - d.z⟩, ?_, hs⟩
    simp only [Box.Overlaps, box, Vec3.shift, halfWidth, height] at hp ⊢
    omega
  · rintro ⟨q, hq, hs⟩
    refine ⟨⟨q.x + d.x, q.y + d.y, q.z + d.z⟩, ?_, ?_⟩
    · simp only [Box.Overlaps, box, Vec3.shift, halfWidth, height] at hq ⊢
      omega
    · have : (⟨q.x + d.x - d.x, q.y + d.y - d.y, q.z + d.z - d.z⟩ : BlockPos) = q := by
        ext <;> simp
      simp only [shiftSolid, this, hs]

theorem contactStep_shift (pos : Vec3) (d : BlockPos) (axis : Axis) (s : Int) :
    contactStep (pos.shift d) axis s = contactStep pos axis s := by
  by_cases h : 0 < s <;> cases axis <;>
    simp only [contactStep, h, ↓reduceIte, box, Vec3.get, Vec3.shift, halfWidth, height] <;>
    omega

theorem moveAxis_shift (solid : BlockPos → Bool) (d : BlockPos) (axis : Axis) (fuel : Nat)
    (pos : Vec3) (dist : Int) :
    moveAxis (shiftSolid solid d) axis fuel (pos.shift d) dist =
      ((moveAxis solid axis fuel pos dist).1.shift d, (moveAxis solid axis fuel pos dist).2) := by
  induction fuel generalizing pos dist with
  | zero => rfl
  | succ fuel ih =>
    simp only [moveAxis, add_shift, blocked_shift, contactStep_shift, ih]
    repeat' split
    all_goals rfl

/--
**Physics is the same everywhere.** Moving the world and the player by any
whole number of blocks and then taking a tick gives the same result as taking
the tick and then moving.
-/
theorem step_shift (solid : BlockPos → Bool) (d : BlockPos) (input : Input) (p : Player) :
    step (shiftSolid solid d) input (p.shift d) = (step solid input p).shift d := by
  simp only [step, shift, moveAxis_shift, add_shift, blocked_shift]
  rfl

end Player

end LeanMc
