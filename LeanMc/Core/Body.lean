import LeanMc.Core.Physics

/-!
# Bodies

A body is a box that moves through the world: the player's, or a creature's.
Its `Shape` says how big the box is, and a `Body` says where it is and how it
is moving.

All movement goes through `Shape.moveAxis`, which advances along one axis in
substeps no longer than any body is wide or tall, checking each destination
before taking it. `LeanMc.Proofs.Body` shows that this never puts a body inside
a solid block and never carries it through one, whatever its shape.
-/

namespace LeanMc

namespace Body

/-- Longest single substep: half a block. No body is narrower or shorter than this. -/
def maxStep : Int := 32768

/-- Fastest movement along one axis: one block per tick. -/
def maxSpeed : Int := 65536

/-- Downward acceleration per tick: 32 blocks per second squared. -/
def gravity : Int := 583

/-- Upward speed at the start of a jump, which carries a body about 1.25 blocks up. -/
def jumpSpeed : Int := 9486

/-- Rounds `Shape.moveAxis` needs for any displacement up to `maxSpeed`. -/
def moveFuel : Nat := 3

def clamp (lo hi v : Int) : Int :=
  max lo (min hi v)

/-- Move a velocity component towards a target, by `rate` sixteenths of the gap. -/
def approach (v target rate : Int) : Int :=
  let gap := target - v
  if gap.natAbs ≤ 16 then target else v + gap * rate / 16

end Body

/-- Where a body is and how it is moving. -/
structure Body where
  /-- Centre of the feet. -/
  pos : Vec3
  /-- Velocity in units per tick. -/
  vel : Vec3 := ⟨0, 0, 0⟩
  onGround : Bool := false
  deriving DecidableEq, Repr

/--
How big a body is. It must be at least as wide and as tall as the longest
substep, so that a substep cannot carry it past a block without touching it.
-/
structure Shape where
  halfWidth : Int
  height : Int
  wide : Body.maxStep ≤ 2 * halfWidth
  tall : Body.maxStep ≤ height

namespace Shape

open Body

/-- The space a body standing at `pos` occupies. -/
def box (sh : Shape) (pos : Vec3) : Box where
  lo := ⟨pos.x - sh.halfWidth, pos.y, pos.z - sh.halfWidth⟩
  hi := ⟨pos.x + sh.halfWidth, pos.y + sh.height, pos.z + sh.halfWidth⟩

/-- Whether a body standing at `pos` would be inside something solid. -/
def blocked (sh : Shape) (solid : BlockPos → Bool) (pos : Vec3) : Bool :=
  (sh.box pos).collides solid

/--
How far a body can move along `axis` towards `s` before its leading face
reaches the next block boundary, and no further than `s` itself.
-/
def contactStep (sh : Shape) (pos : Vec3) (axis : Axis) (s : Int) : Int :=
  if 0 < s then
    let face := (sh.box pos).hi.get axis
    min s ((face + 65535) / 65536 * 65536 - face)
  else
    let face := (sh.box pos).lo.get axis
    max s (face / 65536 * 65536 - face)

/--
Move up to `d` units along `axis`, stopping at the first obstacle. Returns the
new position and whether the move was cut short.

Each round moves at most `maxStep`. If the way is clear it carries on with the
rest; otherwise it closes the remaining gap to the obstacle and stops. `fuel`
bounds the number of rounds.
-/
def moveAxis (sh : Shape) (solid : BlockPos → Bool) (axis : Axis) : Nat → Vec3 → Int → Vec3 × Bool
  | 0, pos, d => (pos, d != 0)
  | fuel + 1, pos, d =>
    if d = 0 then (pos, false)
    else
      let s := clamp (-maxStep) maxStep d
      let next := pos.add axis s
      if sh.blocked solid next then
        let near := pos.add axis (sh.contactStep pos axis s)
        if sh.blocked solid near then (pos, true) else (near, true)
      else sh.moveAxis solid axis fuel next (d - s)

/--
Move a body at `pos` by the velocity `v` for one tick: vertically, then along
`x`, then along `z`. An axis that hits something loses its speed.
-/
def move (sh : Shape) (solid : BlockPos → Bool) (pos v : Vec3) : Body :=
  let my := sh.moveAxis solid .y moveFuel pos v.y
  let mx := sh.moveAxis solid .x moveFuel my.1 v.x
  let mz := sh.moveAxis solid .z moveFuel mx.1 v.z
  { pos := mz.1
    vel := ⟨if mx.2 then 0 else v.x, if my.2 then 0 else v.y, if mz.2 then 0 else v.z⟩
    onGround := sh.blocked solid (mz.1.add .y (-1)) }

/--
Lower a position until it rests on something, trying at most `drop` whole
blocks. Used to set a new body down gently.
-/
def settle (sh : Shape) (solid : BlockPos → Bool) : Nat → Vec3 → Vec3
  | 0, pos => pos
  | drop + 1, pos =>
    let below := pos.add .y (-65536)
    if sh.blocked solid below then pos else sh.settle solid drop below

/-- A body standing still at `pos`, which knows whether there is something to stand on. -/
def resting (sh : Shape) (solid : BlockPos → Bool) (pos : Vec3) : Body :=
  { pos, onGround := sh.blocked solid (pos.add .y (-1)) }

end Shape

end LeanMc
