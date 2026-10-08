/-!
# Coordinates

Three coordinate systems, all integer:

* `BlockPos` names a block anywhere in the unbounded world;
* `ChunkPos` names a chunk, a cube of `16 × 16 × 16` blocks;
* `LocalPos` names a block within a chunk.

`BlockPos.chunkPos` and `BlockPos.localPos` split a block position, and
`ChunkPos.blockAt` puts it back together. Division rounds toward negative
infinity, so the split behaves the same on both sides of the origin.
-/

namespace LeanMc

/-- A block position in the world. Unbounded in every direction. -/
@[ext] structure BlockPos where
  x : Int
  y : Int
  z : Int
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- The position of a chunk, in units of whole chunks. -/
@[ext] structure ChunkPos where
  x : Int
  y : Int
  z : Int
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- A block position within a chunk. -/
@[ext] structure LocalPos where
  x : Fin 16
  y : Fin 16
  z : Fin 16
  deriving DecidableEq, Repr, Inhabited

/-- The six axis directions, which also name the faces of a block. -/
inductive Dir where
  | xp | xn | yp | yn | zp | zn
  deriving DecidableEq, Repr, Inhabited

namespace Dir

def all : List Dir := [xp, xn, yp, yn, zp, zn]

def toNat : Dir → Nat
  | xp => 0 | xn => 1 | yp => 2 | yn => 3 | zp => 4 | zn => 5

/-- The opposite direction. -/
def opp : Dir → Dir
  | xp => xn | xn => xp | yp => yn | yn => yp | zp => zn | zn => zp

end Dir

namespace BlockPos

/-- The neighbouring position one block away in direction `d`. -/
def step (p : BlockPos) : Dir → BlockPos
  | .xp => { p with x := p.x + 1 }
  | .xn => { p with x := p.x - 1 }
  | .yp => { p with y := p.y + 1 }
  | .yn => { p with y := p.y - 1 }
  | .zp => { p with z := p.z + 1 }
  | .zn => { p with z := p.z - 1 }

/-- The chunk containing a block. -/
def chunkPos (p : BlockPos) : ChunkPos :=
  ⟨p.x / 16, p.y / 16, p.z / 16⟩

/-- Where a block sits inside its chunk. -/
def localPos (p : BlockPos) : LocalPos where
  x := ⟨(p.x % 16).toNat, by omega⟩
  y := ⟨(p.y % 16).toNat, by omega⟩
  z := ⟨(p.z % 16).toNat, by omega⟩

end BlockPos

namespace ChunkPos

/-- The neighbouring chunk in direction `d`. -/
def step (c : ChunkPos) : Dir → ChunkPos
  | .xp => { c with x := c.x + 1 }
  | .xn => { c with x := c.x - 1 }
  | .yp => { c with y := c.y + 1 }
  | .yn => { c with y := c.y - 1 }
  | .zp => { c with z := c.z + 1 }
  | .zn => { c with z := c.z - 1 }

/-- The world position of the block at `l` within chunk `c`. -/
def blockAt (c : ChunkPos) (l : LocalPos) : BlockPos :=
  ⟨16 * c.x + (l.x.val : Int), 16 * c.y + (l.y.val : Int), 16 * c.z + (l.z.val : Int)⟩

end ChunkPos

namespace LocalPos

/-- Position of a block in a chunk's flat storage. -/
def index (l : LocalPos) : Fin 4096 :=
  ⟨l.x.val + 16 * l.z.val + 256 * l.y.val, by
    have := l.x.isLt; have := l.y.isLt; have := l.z.isLt; omega⟩

/-- Inverse of `index`. -/
def ofIndex (i : Fin 4096) : LocalPos where
  x := ⟨i.val % 16, by omega⟩
  y := ⟨i.val / 256, by have := i.isLt; omega⟩
  z := ⟨i.val / 16 % 16, by omega⟩

/-- Every local position, in storage order. -/
def all : List LocalPos := (List.finRange 4096).map ofIndex

end LocalPos

end LeanMc
