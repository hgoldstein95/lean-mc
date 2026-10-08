import LeanMc.Core.World
import LeanMc.Proofs.Terrain

/-!
# The generated world

The world the game is played in: generated terrain, with the fast chunk
generator standing in for block-by-block evaluation.
-/

namespace LeanMc.Terrain

/-- The untouched world generated from `seed`. -/
def world (seed : UInt64) : World :=
  World.newWithChunks (generate seed) (generateChunk seed) (generateChunk_get seed)

end LeanMc.Terrain
