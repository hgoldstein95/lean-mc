import LeanMc.Core.Player
import LeanMc.Core.Rng

/-!
# Creatures

An entity is a body with a mind of its own: something in the world that is not
the player and moves without being told to. So far every entity is a fox.

A fox wanders. It picks one of eight directions and a distance of a few blocks,
walks that way, rests a while, and picks again. Where something is in its way
it hops up if it can, and gives up the walk if it cannot. What it picks is
drawn from the game's random number generator, so its wandering is a function
of the game state like everything else.

A fox decides only what velocity it would like; its body keeps that within the
speed limit and `Shape.move` carries it through the world, as it does the
player. So `LeanMc.Proofs.Entity` shows that a fox is never inside a solid
block and never falls through the floor, whatever it decides.

Only creatures in loaded chunks are advanced. The rest are left exactly as
they are until the player comes near again.
-/

namespace LeanMc

structure Entity extends Body where
  /-- The way it faces, in eighths of a turn clockwise from north, which is `-z`. -/
  heading : Fin 8 := 0
  /-- Whether it is walking the way it faces, rather than resting. -/
  walking : Bool := false
  /-- Ticks left before it chooses again what to do. -/
  timer : Nat := 0
  deriving DecidableEq, Repr

namespace Entity

open Body

/-- Half a fox's width: 0.3 blocks. -/
def halfWidth : Int := 19660

/-- A fox's height: 0.7 blocks. -/
def height : Int := 45875

/-- A fox's size. -/
def shape : Shape := ⟨halfWidth, height, by decide, by decide⟩

/-- Walking speed along an axis: about 2.5 blocks per second. -/
def walkSpeed : Int := 2800

/-- Speed along each axis of a diagonal walk, which makes the same speed overall. -/
def diagonalSpeed : Int := 1980

/-- Ticks a walk takes to cover one block. -/
def ticksPerBlock : Nat := 24

/-- How far ahead a fox looks for something in its way: 0.3 blocks. -/
def lookAhead : Int := 19660

/-- The chunk the creature is in. -/
def chunk (e : Entity) : ChunkPos :=
  e.pos.blockPos.chunkPos

/-- The space a fox standing at `pos` occupies. -/
def box (pos : Vec3) : Box :=
  shape.box pos

/-- The step a heading takes along `x` and along `z`: each is -1, 0 or 1. -/
def direction (heading : Fin 8) : Int × Int :=
  match heading.val with
  | 0 => (0, -1) | 1 => (1, -1) | 2 => (1, 0) | 3 => (1, 1)
  | 4 => (0, 1) | 5 => (-1, 1) | 6 => (-1, 0) | _ => (-1, -1)

/-- The horizontal velocity the fox wants: walking speed the way it faces, or none at rest. -/
def wish (e : Entity) : Int × Int :=
  if e.walking then
    let d := direction e.heading
    let speed := if d.1 ≠ 0 ∧ d.2 ≠ 0 then diagonalSpeed else walkSpeed
    (d.1 * speed, d.2 * speed)
  else (0, 0)

/-- Where the fox would be standing a little further the way it faces. -/
def ahead (e : Entity) : Vec3 :=
  let d := direction e.heading
  ⟨e.pos.x + d.1 * lookAhead, e.pos.y, e.pos.z + d.2 * lookAhead⟩

/-- Whether something solid is in the way just ahead. -/
def obstructed (solid : BlockPos → Bool) (e : Entity) : Bool :=
  shape.blocked solid e.ahead

/-- Whether there is room to hop up: nothing a block above the fox, here or just ahead. -/
def climbable (solid : BlockPos → Bool) (e : Entity) : Bool :=
  !shape.blocked solid (e.pos.add .y 65536) && !shape.blocked solid (e.ahead.add .y 65536)

/-- The way a fox sets off, as a random number chooses it. -/
def pickHeading (r : UInt64) : Fin 8 :=
  ⟨r.toNat % 8, Nat.mod_lt _ (by decide)⟩

/-- How long a walk lasts, as a random number chooses it: long enough for two to six blocks. -/
def pickWalk (r : UInt64) : Nat :=
  ticksPerBlock * (2 + r.toNat / 8 % 5)

/-- How long a rest lasts, as a random number chooses it: one to three seconds. -/
def pickRest (r : UInt64) : Nat :=
  60 + r.toNat % 121

/--
Decide what to do this tick. When the timer runs out, a walking fox rests and
a resting fox sets off some way, as a random number chooses. A walking fox
that meets something it cannot climb stops where it is. Otherwise it carries
on.
-/
def think (solid : BlockPos → Bool) (rng : Rng) (e : Entity) : Entity × Rng :=
  if e.timer = 0 then
    let drawn := rng.next
    if e.walking then ({ e with walking := false, timer := pickRest drawn.1 }, drawn.2)
    else
      ({ e with walking := true, heading := pickHeading drawn.1, timer := pickWalk drawn.1 },
        drawn.2)
  else if e.walking && e.obstructed solid && !e.climbable solid then
    ({ e with walking := false, timer := e.timer - 1 }, rng)
  else ({ e with timer := e.timer - 1 }, rng)

/-- Whether the fox hops this tick: it is walking on the ground into something it can climb. -/
def hops (solid : BlockPos → Bool) (e : Entity) : Bool :=
  e.walking && e.onGround && e.obstructed solid && e.climbable solid

/--
The velocity the fox attempts this tick, before anything gets in the way. What
it wishes for is cut down to the speed limit, so no wish can break it.
-/
def intent (solid : BlockPos → Bool) (e : Entity) : Vec3 :=
  let rate : Int := if e.onGround then 8 else 2
  { x := approach e.vel.x (clamp (-maxSpeed) maxSpeed e.wish.1) rate
    y := if e.hops solid then jumpSpeed else max (-maxSpeed) (e.vel.y - gravity)
    z := approach e.vel.z (clamp (-maxSpeed) maxSpeed e.wish.2) rate }

/--
Advance the fox by one tick: it decides what to do, then moves as any body
does. Returns the generator to draw the next random number from.
-/
def step (solid : BlockPos → Bool) (rng : Rng) (e : Entity) : Entity × Rng :=
  let thought := e.think solid rng
  ({ thought.1 with toBody := shape.move solid thought.1.pos (thought.1.intent solid) },
    thought.2)

/--
Advance every creature that is awake by one tick, each drawing from the
generator the one before it left. The others are left as they are.
-/
def stepAll (solid : BlockPos → Bool) (awake : Entity → Bool) :
    Rng → List Entity → List Entity × Rng
  | rng, [] => ([], rng)
  | rng, e :: es =>
    let first := if awake e then e.step solid rng else (e, rng)
    let rest := stepAll solid awake first.2 es
    (first.1 :: rest.1, rest.2)

/--
A fox newly set down at `pos`, facing `heading`. It stands still, knows whether
there is something to stand on, and rests for two seconds before it first sets
off.
-/
def resting (solid : BlockPos → Bool) (pos : Vec3) (heading : Fin 8 := 0) : Entity :=
  { toBody := shape.resting solid pos, heading, timer := 120 }

/-- The same creature, told afresh whether it stands on something. -/
def reground (solid : BlockPos → Bool) (e : Entity) : Entity :=
  { e with onGround := shape.blocked solid (e.pos.add .y (-1)) }

end Entity

end LeanMc
