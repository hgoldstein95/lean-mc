import LeanMc.Core.Player
import LeanMc.Proofs.Body

/-!
# Player physics theorems

The player moves as any body does, so `LeanMc.Proofs.Body` does the work. This
module states what that means for a tick of the player, and adds what is
particular to the player: what velocity they attempt.

* **No clipping.** A player who is not inside a solid block is still not inside
  one after a tick, whatever the input.
* **No tunnelling.** A tick moves the player through a chain of short,
  axis-aligned substeps, each clear of solid blocks from end to end.
* **Standing still is still.** A player at rest on the ground, asking for
  nothing, does not move.
* **Speed is bounded.** No axis of the velocity ever exceeds `maxSpeed`.
* **The floor holds.** Over a solid floor at height zero, the player's feet
  never go below the top of that floor.
* **Physics is the same everywhere.** Shifting the world and the player by any
  whole number of blocks commutes with a tick.
-/

namespace LeanMc

namespace Player

open Body

/-- A player standing at `pos` is not inside any solid block. -/
def Free (solid : BlockPos → Bool) (pos : Vec3) : Prop :=
  shape.Free solid pos

theorem blocked_eq_false_iff {solid : BlockPos → Bool} {pos : Vec3} :
    blocked solid pos = false ↔ Free solid pos :=
  Shape.blocked_eq_false_iff

/-! ## Movement -/

theorem step_pos (solid : BlockPos → Bool) (input : Input) (p : Player) :
    (step solid input p).pos = (shape.move solid p.pos (intent input p)).pos := rfl

/-- A tick moves the player along a path of safe substeps. -/
theorem step_reach (solid : BlockPos → Bool) (input : Input) (p : Player) :
    shape.Reach solid p.pos (step solid input p).pos :=
  shape.move_reach ..

/--
**No clipping.** A player who is not inside a solid block is not inside one
after a tick, whatever the input and however fast they were moving.
-/
theorem step_free {solid : BlockPos → Bool} (input : Input) {p : Player}
    (h : Free solid p.pos) : Free solid (step solid input p).pos :=
  Shape.move_free _ h

/-- The player is reported as on the ground exactly when something solid is directly beneath. -/
theorem step_onGround (solid : BlockPos → Bool) (input : Input) (p : Player) :
    (step solid input p).onGround = false ↔
      Free solid ((step solid input p).pos.add .y (-1)) :=
  blocked_eq_false_iff

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
  have hnot : ¬ (shape.box p.pos).Overlaps q := fun h => by
    rw [hfree q h] at hsolid
    cases hsolid
  have hfeet : p.pos.y = (q.y + 1) * 65536 := by
    simp only [Box.Overlaps, Shape.box, shape, Vec3.add, halfWidth, height] at hq hnot
    omega
  -- So falling is blocked at once, and the gap to close is zero.
  have hintent : intent {} p = ⟨0, -583, 0⟩ := by
    have h0 : clamp (-maxSpeed) maxSpeed 0 = 0 := by decide
    have ha : ∀ r, approach 0 0 r = 0 := fun r => by simp [approach]
    have hg : max (-maxSpeed) (0 - gravity) = -583 := by decide
    simp only [intent, hvel, hfly, h0, ha, hg, Bool.false_bne,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  have hfall : shape.blocked solid (p.pos.add .y (-583)) = true := by
    refine Box.collides_eq_true_iff.mpr ⟨q, ?_, hsolid⟩
    simp only [Box.Overlaps, Shape.box, shape, Vec3.add, halfWidth, height] at hq ⊢
    omega
  have hcontact : shape.contactStep p.pos .y (-583) = 0 := by
    simp only [Shape.contactStep, Shape.box, Vec3.get, hfeet]
    omega
  have hy : shape.moveAxis solid .y moveFuel p.pos (-583) = (p.pos, true) := by
    have hclamp : clamp (-maxStep) maxStep (-583) = -583 := by decide
    have hstay : shape.blocked solid p.pos = false := blocked_eq_false_iff.mpr hfree
    simp [Shape.moveAxis, moveFuel, hclamp, hfall, hcontact, Vec3.add_zero, hstay]
  have hx : ∀ axis, shape.moveAxis solid axis moveFuel p.pos 0 = (p.pos, false) := fun axis =>
    Shape.moveAxis_zero ..
  simp [step, Shape.move, hintent, hy, hx]

/-! ## Speed -/

/-- What the player attempts in a tick is within `maxSpeed` along every axis. -/
theorem intent_bounds (input : Input) {p : Player} (h : p.SpeedBounded) :
    Bounded (intent input p) := by
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
    (h : p.SpeedBounded) : (step solid input p).SpeedBounded :=
  shape.move_speedBounded solid p.pos (intent_bounds input h)

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

/--
**The floor holds.** If the whole layer at height zero is solid, a player whose
feet are above it never ends a tick with their feet below its top.
-/
theorem step_above_floor {solid : BlockPos → Bool} (hfloor : ∀ x z, solid ⟨x, 0, z⟩ = true)
    (input : Input) {p : Player} (h : 65536 ≤ p.pos.y) : 65536 ≤ (step solid input p).pos.y :=
  Shape.move_above_floor hfloor _ h

/-! ## Translation invariance -/

/-- The player moved by a whole number of blocks. -/
def shift (p : Player) (d : BlockPos) : Player :=
  { p with pos := p.pos.shift d }

/--
**Physics is the same everywhere.** Moving the world and the player by any
whole number of blocks and then taking a tick gives the same result as taking
the tick and then moving.
-/
theorem step_shift (solid : BlockPos → Bool) (d : BlockPos) (input : Input) (p : Player) :
    step (shiftSolid solid d) input (p.shift d) = (step solid input p).shift d := by
  simp only [step, shift, Shape.move_shift, Body.shift]
  rfl

end Player

end LeanMc
