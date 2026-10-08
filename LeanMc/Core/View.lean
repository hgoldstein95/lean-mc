import LeanMc.Core.Mesh
import LeanMc.Core.World
import LeanMc.Core.Physics

/-!
# What to keep loaded and what to rebuild

Two decisions the renderer depends on, kept here so that they can be proved:

* which chunks are in view of a given chunk, and which are far enough away to
  drop; and
* which chunks' meshes a block change can affect.

Getting either wrong shows as holes in the world or as faces that linger after
a block has gone.
-/

namespace LeanMc

/-- How far the view extends, in chunks: `radius` horizontally and `radiusY` vertically. -/
structure ViewRange where
  radius : Nat
  radiusY : Nat

namespace ViewRange

/-- Whether chunk `c` is in view from chunk `centre`, with the range widened by `slack`. -/
def contains (v : ViewRange) (centre c : ChunkPos) (slack : Nat := 0) : Bool :=
  (c.x - centre.x).natAbs ≤ v.radius + slack
    && (c.y - centre.y).natAbs ≤ v.radiusY + slack
    && (c.z - centre.z).natAbs ≤ v.radius + slack

/-- Every offset from a centre chunk to a chunk in view, in no particular order. -/
def offsets (v : ViewRange) : List (Int × Int × Int) :=
  (intRange (-v.radius) v.radius).flatMap fun dx =>
    (intRange (-v.radiusY) v.radiusY).flatMap fun dy =>
      (intRange (-v.radius) v.radius).map fun dz => (dx, dy, dz)

/-- The chunk at an offset from a centre. -/
def offsetChunk (centre : ChunkPos) (o : Int × Int × Int) : ChunkPos :=
  ⟨centre.x + o.1, centre.y + o.2.1, centre.z + o.2.2⟩

/-- Whether chunk `c` is far enough from `centre` to be dropped. -/
def isFar (v : ViewRange) (centre c : ChunkPos) (slack : Nat) : Bool :=
  !v.contains centre c slack

end ViewRange

/--
The chunks whose meshes can change when the block at `p` changes: the chunk
holding `p`, and the chunks holding its six neighbours.
-/
def dirtyChunks (p : BlockPos) : List ChunkPos :=
  (p.chunkPos :: Dir.all.map fun d => (p.step d).chunkPos).eraseDups

end LeanMc
