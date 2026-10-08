import LeanMc.Core.World
import LeanMc.Proofs.Chunk

/-!
# World storage theorems

* Reads and writes obey the usual laws: a write is seen at its own position
  and changes nothing else, including across chunk boundaries.
* A position nobody has written still holds its terrain block.
* Materialised chunks and the chunk cache agree with the world, so loading and
  unloading chunks can never lose or invent a block.
-/

namespace LeanMc

namespace World

@[simp] theorem get_new (terrain : BlockPos → Block) (p : BlockPos) :
    (new terrain).get p = terrain p := by
  simp [new, get]

theorem get_set_self (w : World) (p : BlockPos) (b : Block) : (w.set p b).get p = b := by
  simp [get, set]

theorem get_set_of_ne (w : World) {p q : BlockPos} (b : Block) (h : q ≠ p) :
    (w.set p b).get q = w.get q := by
  simp [get, set, Std.HashMap.getElem?_insert, Ne.symm h]

theorem get_set (w : World) (p q : BlockPos) (b : Block) :
    (w.set p b).get q = if q = p then b else w.get q := by
  split
  · subst_vars; exact get_set_self ..
  · exact get_set_of_ne _ _ ‹_›

/-- Writing never changes the terrain underneath. -/
@[simp] theorem terrain_set (w : World) (p : BlockPos) (b : Block) :
    (w.set p b).terrain = w.terrain := rfl

/-- A later write to the same position wins. -/
theorem get_set_set (w : World) (p q : BlockPos) (a b : Block) :
    ((w.set p a).set p b).get q = (w.set p b).get q := by
  simp only [get_set]
  split <;> rfl

/-- Writes to different positions can be made in either order. -/
theorem get_set_comm (w : World) {p p' : BlockPos} (q : BlockPos) (a b : Block) (h : p ≠ p') :
    ((w.set p a).set p' b).get q = ((w.set p' b).set p a).get q := by
  simp only [get_set]
  split <;> split <;> simp_all

theorem get_setMany_of_not_mem (w : World) (edits : List (BlockPos × Block)) (p : BlockPos)
    (h : ∀ e ∈ edits, e.1 ≠ p) : (w.setMany edits).get p = w.get p := by
  induction edits generalizing w with
  | nil => rfl
  | cons e es ih =>
    simp only [setMany, List.foldl_cons]
    have := ih (w.set e.1 e.2) (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    simp only [setMany] at this
    rw [this, get_set_of_ne _ _ (Ne.symm (h e List.mem_cons_self))]

/-- However the world has been edited, a position nobody wrote still holds its terrain block. -/
theorem get_setMany_new (terrain : BlockPos → Block) (edits : List (BlockPos × Block))
    (p : BlockPos) (h : ∀ e ∈ edits, e.1 ≠ p) :
    ((new terrain).setMany edits).get p = terrain p := by
  rw [get_setMany_of_not_mem _ _ _ h, get_new]

/-- A materialised chunk holds exactly the world's blocks. -/
theorem get_chunk (w : World) (c : ChunkPos) (l : LocalPos) :
    (w.chunk c).get l = w.get (c.blockAt l) := by
  simp [chunk, Chunk.get_ofFn]

/-- Reading any block through its materialised chunk gives the world's block. -/
theorem get_chunk_chunkPos (w : World) (p : BlockPos) :
    (w.chunk p.chunkPos).get p.localPos = w.get p := by
  rw [get_chunk, BlockPos.blockAt_chunkPos_localPos]

/--
A write changes one block of one chunk: the chunk holding `p` is updated at
`p`'s local position and every other chunk is untouched.
-/
theorem chunk_set (w : World) (p : BlockPos) (b : Block) (c : ChunkPos) :
    (w.set p b).chunk c =
      if c = p.chunkPos then (w.chunk c).set p.localPos b else w.chunk c := by
  apply Chunk.ext_get
  intro l
  rw [get_chunk, get_set]
  split
  · next h =>
    obtain ⟨hc, hl⟩ := BlockPos.eq_blockAt_iff.mp h.symm
    simp [← hc, ← hl, Chunk.get_set_self]
  · next h =>
    split
    · next hc =>
      have hl : l ≠ p.localPos := fun hl => h (BlockPos.eq_blockAt_iff.mpr ⟨hc.symm, hl.symm⟩).symm
      rw [Chunk.get_set_of_ne _ _ hl, get_chunk]
    · rw [get_chunk]

end World

namespace ChunkCache

/-- Every chunk the cache holds is exactly the world's chunk at that position. -/
def Valid (cache : ChunkCache) (w : World) : Prop :=
  ∀ c chunk, cache.chunks[c]? = some chunk → chunk = w.chunk c

theorem valid_empty (w : World) : ({} : ChunkCache).Valid w := by
  intro c chunk h
  simp at h

/-- Reading through a valid cache is the same as reading the world. -/
theorem Valid.blockAt_eq {cache : ChunkCache} {w : World} (h : cache.Valid w) (p : BlockPos) :
    cache.blockAt w p = w.get p := by
  unfold blockAt
  split
  · next chunk hc => rw [h _ _ hc, World.get_chunk_chunkPos]
  · rfl

theorem Valid.load {cache : ChunkCache} {w : World} (h : cache.Valid w) (c : ChunkPos) :
    (cache.load w c).Valid w := by
  unfold ChunkCache.load
  split
  · exact h
  · intro c' chunk hc
    simp only [Std.HashMap.getElem?_insert] at hc
    split at hc
    · next heq => simp_all
    · exact h _ _ hc

theorem Valid.unload {cache : ChunkCache} {w : World} (h : cache.Valid w) (c : ChunkPos) :
    (cache.unload c).Valid w := by
  intro c' chunk hc
  have hc : (cache.chunks.erase c)[c']? = some chunk := hc
  rw [Std.HashMap.getElem?_erase] at hc
  by_cases e : c = c'
  · simp [e] at hc
  · simp only [beq_iff_eq, e, ite_false] at hc
    exact h _ _ hc

/-- Mirroring a write in the cache keeps it in step with the world. -/
theorem Valid.setBlock {cache : ChunkCache} {w : World} (h : cache.Valid w) (p : BlockPos)
    (b : Block) : (cache.setBlock p b).Valid (w.set p b) := by
  intro c chunk hc
  have hc : (cache.chunks.modify p.chunkPos (·.set p.localPos b))[c]? = some chunk := hc
  rw [Std.HashMap.getElem?_modify] at hc
  rw [World.chunk_set]
  by_cases e : p.chunkPos = c
  · subst e
    cases hold : cache.chunks[p.chunkPos]? with
    | none => simp [hold] at hc
    | some old =>
      simp only [beq_self_eq_true, ite_true, hold, Option.map_some, Option.some.injEq] at hc
      simp [← hc, h _ _ hold]
  · simp only [beq_iff_eq, e, ite_false] at hc
    simp [Ne.symm e, h _ _ hc]

/--
Loading and unloading chunks in any order never changes what is read: the
world, not the cache, is the source of truth.
-/
theorem Valid.blockAt_load_unload {cache : ChunkCache} {w : World} (h : cache.Valid w)
    (c : ChunkPos) (p : BlockPos) : ((cache.unload c).load w c).blockAt w p = w.get p :=
  ((h.unload c).load c).blockAt_eq p

end ChunkCache

end LeanMc
