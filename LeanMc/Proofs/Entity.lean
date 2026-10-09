import LeanMc.Core.Entity
import LeanMc.Proofs.Body

/-!
# Creature theorems

A fox moves as any body does, so `LeanMc.Proofs.Body` does the work. This
module states what that means for a tick of a fox.

* **Thinking does not move.** Deciding what to do changes where a fox means to
  go, never where it is.
* **A fox stays sound.** A fox that is clear of blocks, above the floor and
  within the speed limit is still all three after a tick, whatever it decides
  and whatever random numbers it draws, and it knows whether it stands on
  something.
* **So does every creature**, awake or not, and advancing them neither makes
  creatures nor loses them.
* **Asleep means untouched.** A creature that is not awake is exactly as it was.
-/

namespace LeanMc

namespace Entity

open Body

/-- A creature with nothing wrong with it, in a world with these solid blocks. -/
structure Sound (solid : BlockPos → Bool) (e : Entity) : Prop where
  /-- It is not inside a solid block. -/
  free : shape.Free solid e.pos
  /-- Its feet are above the floor. -/
  above : 65536 ≤ e.pos.y
  /-- No axis of its velocity is beyond the speed limit. -/
  speed : e.SpeedBounded
  /-- It knows whether it is standing on something. -/
  grounded : e.onGround = shape.blocked solid (e.pos.add .y (-1))

theorem sound_iff {solid : BlockPos → Bool} {e : Entity} :
    e.Sound solid ↔ shape.blocked solid e.pos = false ∧ 65536 ≤ e.pos.y ∧ e.SpeedBounded
      ∧ e.onGround = shape.blocked solid (e.pos.add .y (-1)) :=
  ⟨fun h => ⟨Shape.blocked_eq_false_iff.mpr h.free, h.above, h.speed, h.grounded⟩,
    fun h => ⟨Shape.blocked_eq_false_iff.mp h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

instance (solid : BlockPos → Bool) (e : Entity) : Decidable (e.Sound solid) :=
  decidable_of_iff _ sound_iff.symm

/-- **Thinking does not move.** Deciding what to do leaves the fox's body as it was. -/
theorem think_toBody (solid : BlockPos → Bool) (rng : Rng) (e : Entity) :
    (e.think solid rng).1.toBody = e.toBody := by
  unfold think
  repeat' split
  all_goals rfl

theorem step_pos (solid : BlockPos → Bool) (rng : Rng) (e : Entity) :
    (e.step solid rng).1.pos
      = (shape.move solid e.pos ((e.think solid rng).1.intent solid)).pos := by
  simp only [step, think_toBody]

/-- What a fox attempts in a tick is within `maxSpeed` along every axis, whatever it wishes. -/
theorem intent_bounds (solid : BlockPos → Bool) {e : Entity} (h : e.SpeedBounded) :
    Bounded (e.intent solid) := by
  obtain ⟨hx, hy, hz⟩ := h
  have hr : ∀ b : Bool, (0 : Int) ≤ (if b then 8 else 2) ∧ (if b then 8 else 2 : Int) ≤ 16 := by
    intro b; cases b <;> decide
  have cx := clamp_bounds (lo := -maxSpeed) (hi := maxSpeed) (by decide) e.wish.1
  have cz := clamp_bounds (lo := -maxSpeed) (hi := maxSpeed) (by decide) e.wish.2
  refine ⟨approach_bounds (hr _) hx cx, ?_, approach_bounds (hr _) hz cz⟩
  simp only [intent, maxSpeed, jumpSpeed, gravity] at hy ⊢
  split <;> omega

/--
**A fox stays sound.** Over a solid floor, a fox that is clear of blocks, above
the floor and within the speed limit is sound after a tick, whatever it decides
to do and whatever random numbers it draws.
-/
theorem step_sound {solid : BlockPos → Bool} (hfloor : ∀ x z, solid ⟨x, 0, z⟩ = true) (rng : Rng)
    {e : Entity} (hfree : shape.Free solid e.pos) (habove : 65536 ≤ e.pos.y)
    (hspeed : e.SpeedBounded) : (e.step solid rng).1.Sound solid where
  free := by
    rw [step_pos]
    exact Shape.move_free _ hfree
  above := by
    rw [step_pos]
    exact Shape.move_above_floor hfloor _ habove
  speed := by
    have : (e.think solid rng).1.SpeedBounded := by
      rw [SpeedBounded, think_toBody]
      exact hspeed
    exact shape.move_speedBounded solid _ (intent_bounds solid this)
  grounded := rfl

/-- Advancing the creatures neither makes creatures nor loses them. -/
theorem stepAll_length (solid : BlockPos → Bool) (awake : Entity → Bool) (rng : Rng)
    (es : List Entity) : (stepAll solid awake rng es).1.length = es.length := by
  induction es generalizing rng with
  | nil => rfl
  | cons e es ih => simp [stepAll, ih]

/-- **Asleep means untouched.** A creature that is not awake is exactly as it was, where it was. -/
theorem stepAll_asleep (solid : BlockPos → Bool) {awake : Entity → Bool} (rng : Rng)
    {es : List Entity} {i : Nat} {e : Entity} (he : es[i]? = some e) (ha : awake e = false) :
    (stepAll solid awake rng es).1[i]? = some e := by
  induction es generalizing rng i with
  | nil => simp at he
  | cons e' es ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst he
      simp [stepAll, ha]
    | succ i =>
      simp only [List.getElem?_cons_succ] at he
      simp only [stepAll, List.getElem?_cons_succ]
      exact ih _ he

/--
**Every creature stays sound.** Each must be clear of blocks, above the floor
and within the speed limit. One that is awake then learns whether it stands on
something; one that is not must know already.
-/
theorem stepAll_sound {solid : BlockPos → Bool} (hfloor : ∀ x z, solid ⟨x, 0, z⟩ = true)
    (awake : Entity → Bool) (rng : Rng) {es : List Entity}
    (h : ∀ e ∈ es, shape.Free solid e.pos ∧ 65536 ≤ e.pos.y ∧ e.SpeedBounded)
    (hg : ∀ e ∈ es, awake e = false → e.onGround = shape.blocked solid (e.pos.add .y (-1))) :
    ∀ e ∈ (stepAll solid awake rng es).1, e.Sound solid := by
  induction es generalizing rng with
  | nil =>
    intro e he
    cases he
  | cons e es ih =>
    intro e' he'
    simp only [stepAll, List.mem_cons] at he'
    rcases he' with rfl | he'
    · obtain ⟨hf, ha, hs⟩ := h e List.mem_cons_self
      cases hw : awake e with
      | true =>
        simp only [↓reduceIte]
        exact step_sound hfloor rng hf ha hs
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨hf, ha, hs, hg e List.mem_cons_self hw⟩
    · exact ih _ (fun e he => h e (List.mem_cons_of_mem _ he))
        (fun e he => hg e (List.mem_cons_of_mem _ he)) e' he'

theorem resting_pos (solid : BlockPos → Bool) (pos : Vec3) (heading : Fin 8) :
    (resting solid pos heading).pos = pos := rfl

theorem resting_onGround (solid : BlockPos → Bool) (pos : Vec3) (heading : Fin 8) :
    (resting solid pos heading).onGround = shape.blocked solid (pos.add .y (-1)) := rfl

/-- A fox set down somewhere clear and above the floor is sound: it is at rest and grounded. -/
theorem resting_sound {solid : BlockPos → Bool} {pos : Vec3} (heading : Fin 8)
    (hfree : shape.Free solid pos) (habove : 65536 ≤ pos.y) :
    (resting solid pos heading).Sound solid where
  free := hfree
  above := habove
  speed := by
    show Bounded ⟨0, 0, 0⟩
    decide
  grounded := rfl

end Entity

end LeanMc
