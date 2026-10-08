import LeanMc.Core.Block
import LeanMc.Core.Pos

/-!
# Chunks

A chunk stores the `16 × 16 × 16` blocks of one cube of the world in a flat
vector, addressed by `LocalPos`.
-/

namespace LeanMc

@[ext] structure Chunk where
  blocks : Vector Block 4096

namespace Chunk

def get (c : Chunk) (l : LocalPos) : Block :=
  c.blocks[l.index]

def set (c : Chunk) (l : LocalPos) (b : Block) : Chunk :=
  ⟨c.blocks.set l.index b⟩

/-- The chunk whose block at each local position is given by `f`. -/
def ofFn (f : LocalPos → Block) : Chunk :=
  ⟨Vector.ofFn fun i => f (LocalPos.ofIndex i)⟩

end Chunk

end LeanMc
