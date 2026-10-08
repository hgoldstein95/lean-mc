import LeanMc.Core.Generated
import LeanMc.Proofs.World
import LeanMc.Proofs.Mesh

/-!
# Theorems about the generated world

These tie the pieces together for the world the game actually runs: its chunks
are a function of the seed and position alone, and what is drawn is exactly
what the terrain and the edits say should be visible.
-/

namespace LeanMc.Terrain

@[simp] theorem world_get (seed : UInt64) (p : BlockPos) : (world seed).get p = generate seed p := by
  simp [world, World.newWithChunks, World.get]

/--
**Generation does not depend on order.** A chunk of the untouched world holds
exactly the terrain function's blocks, whichever chunks were generated before
it and however often it has been generated.
-/
theorem world_chunk_get (seed : UInt64) (c : ChunkPos) (l : LocalPos) :
    ((world seed).chunk c).get l = generate seed (c.blockAt l) := by
  rw [World.get_chunk, world_get]

/-- After any edits, a position nobody wrote still holds its generated block. -/
theorem world_setMany_get (seed : UInt64) (edits : List (BlockPos × Block)) (p : BlockPos)
    (h : ∀ e ∈ edits, e.1 ≠ p) : ((world seed).setMany edits).get p = generate seed p := by
  rw [World.get_setMany_of_not_mem _ _ _ h, world_get]

/--
**What is drawn is what is there.** Through any valid chunk cache and after any
edits, a face is in a chunk's mesh exactly when the world's block there is
visible and the world's block beside it is not opaque.
-/
theorem mem_chunkFaces_cache {cache : ChunkCache} {w : World} (h : cache.Valid w) {c : ChunkPos}
    {f : Face} :
    f ∈ chunkFaces (cache.blockAt w) c ↔
      faceVisible w.get (c.blockAt f.pos) f.dir = true ∧ f.block = w.get (c.blockAt f.pos) := by
  have : cache.blockAt w = w.get := funext h.blockAt_eq
  rw [this, mem_chunkFaces]

end LeanMc.Terrain
