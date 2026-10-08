import LeanMc.Core.Physics

/-!
# The player

The player is a box that walks, falls, jumps and optionally flies. One call to
`Player.step` advances it by one tick, a sixtieth of a second.

All movement goes through `moveAxis`, which advances along one axis in
substeps no longer than the player is wide, checking each destination before
taking it. `LeanMc.Proofs.Player` shows that this never puts the player inside
a solid block and never carries it through one.
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

/-- Longest single substep: half a block, which is less than the player's width and height. -/
def maxStep : Int := 32768

/-- Fastest movement along one axis: one block per tick. -/
def maxSpeed : Int := 65536

/-- Downward acceleration per tick: 32 blocks per second squared. -/
def gravity : Int := 583

/-- Upward speed at the start of a jump, which carries the player about 1.25 blocks up. -/
def jumpSpeed : Int := 9486

def walkSpeed : Int := 4697
def sprintSpeed : Int := 6117
def flySpeed : Int := 11906
def fastFlySpeed : Int := 43691

end Player

structure Player where
  /-- Centre of the feet. -/
  pos : Vec3
  /-- Velocity in units per tick. -/
  vel : Vec3 := ⟨0, 0, 0⟩
  onGround : Bool := false
  flying : Bool := false
  deriving Repr

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

/-- The space a player standing at `pos` occupies. -/
def box (pos : Vec3) : Box where
  lo := ⟨pos.x - halfWidth, pos.y, pos.z - halfWidth⟩
  hi := ⟨pos.x + halfWidth, pos.y + height, pos.z + halfWidth⟩

/-- Whether a player standing at `pos` would be inside something solid. -/
def blocked (solid : BlockPos → Bool) (pos : Vec3) : Bool :=
  (box pos).collides solid

def clamp (lo hi v : Int) : Int :=
  max lo (min hi v)

/--
How far the player can move along `axis` towards `s` before its leading face
reaches the next block boundary, and no further than `s` itself.
-/
def contactStep (pos : Vec3) (axis : Axis) (s : Int) : Int :=
  if 0 < s then
    let face := (box pos).hi.get axis
    min s ((face + 65535) / 65536 * 65536 - face)
  else
    let face := (box pos).lo.get axis
    max s (face / 65536 * 65536 - face)

/--
Move up to `d` units along `axis`, stopping at the first obstacle. Returns the
new position and whether the move was cut short.

Each round moves at most `maxStep`. If the way is clear it carries on with the
rest; otherwise it closes the remaining gap to the obstacle and stops. `fuel`
bounds the number of rounds.
-/
def moveAxis (solid : BlockPos → Bool) (axis : Axis) : Nat → Vec3 → Int → Vec3 × Bool
  | 0, pos, d => (pos, d != 0)
  | fuel + 1, pos, d =>
    if d = 0 then (pos, false)
    else
      let s := clamp (-maxStep) maxStep d
      let next := pos.add axis s
      if blocked solid next then
        let near := pos.add axis (contactStep pos axis s)
        if blocked solid near then (pos, true) else (near, true)
      else moveAxis solid axis fuel next (d - s)

/-- Rounds `moveAxis` needs for any displacement up to `maxSpeed`. -/
def moveFuel : Nat := 3

/-- Move a velocity component towards a target, by `rate` sixteenths of the gap. -/
def approach (v target rate : Int) : Int :=
  let gap := target - v
  if gap.natAbs ≤ 16 then target else v + gap * rate / 16

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
  let v := intent input p
  let my := moveAxis solid .y moveFuel p.pos v.y
  let mx := moveAxis solid .x moveFuel my.1 v.x
  let mz := moveAxis solid .z moveFuel mx.1 v.z
  { pos := mz.1
    vel := ⟨if mx.2 then 0 else v.x, if my.2 then 0 else v.y, if mz.2 then 0 else v.z⟩
    onGround := blocked solid (mz.1.add .y (-1))
    flying := p.flying != input.toggleFly }

/--
Lower a position until it rests on something, trying at most `drop` whole
blocks. Used to set a new player down gently.
-/
def settle (solid : BlockPos → Bool) : Nat → Vec3 → Vec3
  | 0, pos => pos
  | drop + 1, pos =>
    let below := pos.add .y (-65536)
    if blocked solid below then pos else settle solid drop below

end Player

end LeanMc
