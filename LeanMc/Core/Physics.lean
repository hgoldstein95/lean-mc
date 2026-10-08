import LeanMc.Core.Pos

/-!
# Fixed-point geometry

Positions and velocities in the simulation are integers, in units of 1/65536
of a block. Arithmetic on them is exact and behaves identically everywhere in
the world, which floating point cannot offer.

A `Box` is an axis-aligned box that is closed below and open above, so a box
resting on a block's top face touches the block without overlapping it.
-/

namespace LeanMc

/-- Fixed-point units in one block. -/
def unitsPerBlock : Int := 65536

/-- A point or displacement in fixed-point units. -/
@[ext] structure Vec3 where
  x : Int
  y : Int
  z : Int
  deriving DecidableEq, Repr, Inhabited

inductive Axis where
  | x | y | z
  deriving DecidableEq, Repr

namespace Vec3

def get (v : Vec3) : Axis → Int
  | .x => v.x
  | .y => v.y
  | .z => v.z

/-- Move `d` units along one axis. -/
def add (v : Vec3) : Axis → Int → Vec3
  | .x, d => { v with x := v.x + d }
  | .y, d => { v with y := v.y + d }
  | .z, d => { v with z := v.z + d }

/-- Move by a whole number of blocks. -/
def shift (v : Vec3) (d : BlockPos) : Vec3 :=
  ⟨v.x + d.x * 65536, v.y + d.y * 65536, v.z + d.z * 65536⟩

/-- The block containing a point. -/
def blockPos (v : Vec3) : BlockPos :=
  ⟨v.x / 65536, v.y / 65536, v.z / 65536⟩

end Vec3

/-- The half-open box `[lo, hi)`. -/
structure Box where
  lo : Vec3
  hi : Vec3
  deriving Repr

/-- The integers from `lo` to `hi` inclusive. -/
def intRange (lo hi : Int) : List Int :=
  (List.range (hi - lo + 1).toNat).map fun (i : Nat) => lo + (i : Int)

/-- Block coordinates overlapped along one axis by the interval `[lo, hi)`. -/
def blockRange (lo hi : Int) : List Int :=
  intRange (lo / 65536) ((hi - 1) / 65536)

namespace Box

/-- Whether the box overlaps any solid block. -/
def collides (solid : BlockPos → Bool) (b : Box) : Bool :=
  (blockRange b.lo.x b.hi.x).any fun x =>
    (blockRange b.lo.y b.hi.y).any fun y =>
      (blockRange b.lo.z b.hi.z).any fun z =>
        solid ⟨x, y, z⟩

end Box

end LeanMc
