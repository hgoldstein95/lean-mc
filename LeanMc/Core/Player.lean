import LeanMc.Core.Body

/-!
# The player

The player is a body that walks, falls, jumps and optionally flies. One call to
`Player.step` advances it by one tick, a sixtieth of a second.

The player decides only what velocity to attempt; `Shape.move` carries it
through the world. `LeanMc.Proofs.Player` shows that this never puts the
player inside a solid block and never carries it through one.
-/

namespace LeanMc

/-- Ticks simulated per second. -/
def ticksPerSecond : Nat := 60

namespace Player

/-- Half the player's width: 0.3 blocks. -/
def halfWidth : Int := 19660

/-- The player's height: 1.8 blocks. -/
def height : Int := 117964

/-- Height of the eyes above the feet: 1.62 blocks. -/
def eyeHeight : Int := 106168

def walkSpeed : Int := 4697
def sprintSpeed : Int := 6117
def flySpeed : Int := 11906
def fastFlySpeed : Int := 43691

/-- The player's size. -/
def shape : Shape := ⟨halfWidth, height, by decide, by decide⟩

end Player

structure Player extends Body where
  flying : Bool := false
  deriving DecidableEq, Repr

/-- What the player is trying to do this tick. -/
structure Input where
  /-- Desired horizontal velocity, in units per tick. -/
  wishX : Int := 0
  wishZ : Int := 0
  /-- Jump, or rise when flying. -/
  jump : Bool := false
  /-- Sink when flying. -/
  descend : Bool := false
  toggleFly : Bool := false
  deriving Repr

namespace Player

open Body

/-- The space a player standing at `pos` occupies. -/
def box (pos : Vec3) : Box :=
  shape.box pos

/-- Whether a player standing at `pos` would be inside something solid. -/
def blocked (solid : BlockPos → Bool) (pos : Vec3) : Bool :=
  shape.blocked solid pos

/-- The velocity the player attempts this tick, before anything gets in the way. -/
def intent (input : Input) (p : Player) : Vec3 :=
  let flying := p.flying != input.toggleFly
  let rate : Int := if flying || p.onGround then 8 else 2
  { x := approach p.vel.x (clamp (-maxSpeed) maxSpeed input.wishX) rate
    y :=
      if flying then
        (if input.jump then flySpeed else 0) - (if input.descend then flySpeed else 0)
      else if input.jump && p.onGround then jumpSpeed
      else max (-maxSpeed) (p.vel.y - gravity)
    z := approach p.vel.z (clamp (-maxSpeed) maxSpeed input.wishZ) rate }

/-- Advance the player by one tick: move vertically, then along `x`, then along `z`. -/
def step (solid : BlockPos → Bool) (input : Input) (p : Player) : Player :=
  { toBody := shape.move solid p.pos (intent input p)
    flying := p.flying != input.toggleFly }

/-- Where the player's eyes are. -/
def eye (p : Player) : Vec3 :=
  p.pos.add .y eyeHeight

/-- The chunk the player's eyes are in. The world is loaded around it. -/
def chunk (p : Player) : ChunkPos :=
  p.eye.blockPos.chunkPos

/-- A player standing still at `pos`, who knows whether there is something to stand on. -/
def resting (solid : BlockPos → Bool) (pos : Vec3) : Player :=
  { pos, onGround := blocked solid (pos.add .y (-1)) }

end Player

end LeanMc
