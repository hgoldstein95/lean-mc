import LeanMc.Core.Physics

/-!
# Block targeting

Finds the block the player is looking at by walking, cell by cell, along the
segment from the eyes to the limit of their reach. Each step moves to the
face-adjacent cell the segment enters next, so the walk is a chain of
neighbouring cells; it stops at the first solid one.

Arithmetic is exact: crossing times are compared as integer fractions.
-/

namespace LeanMc

/-- The result of looking at a block. -/
structure RayHit where
  /-- The solid block the walk stopped at. -/
  block : BlockPos
  /-- The side of that block the walk came in through; `none` if it started inside the block. -/
  face : Option Dir
  deriving DecidableEq, Repr

namespace Ray

/--
Whether the segment from `o` to `o + d` goes on past cell `c` in direction
`dir`: its far end lies beyond that face of the cell.
-/
def crosses (o d : Vec3) (c : BlockPos) : Dir → Bool
  | .xp => decide ((c.x + 1) * 65536 ≤ o.x + d.x)
  | .xn => decide (o.x + d.x < c.x * 65536)
  | .yp => decide ((c.y + 1) * 65536 ≤ o.y + d.y)
  | .yn => decide (o.y + d.y < c.y * 65536)
  | .zp => decide ((c.z + 1) * 65536 ≤ o.z + d.z)
  | .zn => decide (o.z + d.z < c.z * 65536)

/--
When the segment reaches the face of `c` in direction `dir`, as a fraction of
the way along it: numerator and denominator.
-/
def crossTime (o d : Vec3) (c : BlockPos) : Dir → Int × Int
  | .xp => ((c.x + 1) * 65536 - o.x, d.x)
  | .xn => (o.x - c.x * 65536, -d.x)
  | .yp => ((c.y + 1) * 65536 - o.y, d.y)
  | .yn => (o.y - c.y * 65536, -d.y)
  | .zp => ((c.z + 1) * 65536 - o.z, d.z)
  | .zn => (o.z - c.z * 65536, -d.z)

/-- Whether fraction `a` is no later than fraction `b`, for positive denominators. -/
def sooner (a b : Int × Int) : Bool :=
  a.1 * b.2 ≤ b.1 * a.2

/-- Keep whichever of two candidate exits the segment reaches first. -/
def pick (o d : Vec3) (c : BlockPos) (best : Option Dir) (dir : Dir) : Option Dir :=
  match best with
  | none => some dir
  | some b => if sooner (crossTime o d c b) (crossTime o d c dir) then some b else some dir

/-- The face through which the segment leaves cell `c`, if it leaves it at all. -/
def nextStep (o d : Vec3) (c : BlockPos) : Option Dir :=
  (Dir.all.filter (crosses o d c)).foldl (pick o d c) none

/--
Walk from cell `c` along the segment, stopping at the first solid cell.
`entered` is the direction of the step that brought the walk into `c`.
-/
def castFrom (solid : BlockPos → Bool) (o d : Vec3) : Nat → BlockPos → Option Dir → Option RayHit
  | 0, _, _ => none
  | fuel + 1, c, entered =>
    if solid c then some ⟨c, entered.map Dir.opp⟩
    else
      match nextStep o d c with
      | none => none
      | some dir => castFrom solid o d fuel (c.step dir) (some dir)

/--
How many more cells the walk can enter from `c`: the distance, cell by cell
along each axis, to the cell holding the far end of the segment.
-/
def remaining (o d : Vec3) (c : BlockPos) : Nat :=
  ((o.x + d.x) / 65536 - c.x).natAbs + ((o.y + d.y) / 65536 - c.y).natAbs
    + ((o.z + d.z) / 65536 - c.z).natAbs

/-- The first solid block along the segment from `o` to `o + d`, however long it is. -/
def cast (solid : BlockPos → Bool) (o d : Vec3) : Option RayHit :=
  castFrom solid o d (remaining o d o.blockPos + 1) o.blockPos none

end Ray

end LeanMc
