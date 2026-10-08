import LeanMc.Core.Pos

/-!
# Coordinate theorems

Splitting a block position into a chunk and a local position loses nothing and
invents nothing, on both sides of the origin; and a chunk's flat storage index
is a bijection with its local positions.
-/

namespace LeanMc

namespace BlockPos

/-- Splitting a position and putting it back together gives the same position. -/
theorem blockAt_chunkPos_localPos (p : BlockPos) : p.chunkPos.blockAt p.localPos = p := by
  ext <;> simp [ChunkPos.blockAt, chunkPos, localPos] <;> omega

end BlockPos

namespace ChunkPos

theorem chunkPos_blockAt (c : ChunkPos) (l : LocalPos) : (c.blockAt l).chunkPos = c := by
  ext <;> simp [blockAt, BlockPos.chunkPos] <;> omega

theorem localPos_blockAt (c : ChunkPos) (l : LocalPos) : (c.blockAt l).localPos = l := by
  ext <;> simp [blockAt, BlockPos.localPos] <;> omega

/-- Distinct (chunk, local) pairs name distinct blocks. -/
theorem blockAt_inj {c c' : ChunkPos} {l l' : LocalPos} :
    c.blockAt l = c'.blockAt l' ↔ c = c' ∧ l = l' := by
  constructor
  · intro h
    have hc := congrArg BlockPos.chunkPos h
    have hl := congrArg BlockPos.localPos h
    simp only [chunkPos_blockAt, localPos_blockAt] at hc hl
    exact ⟨hc, hl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end ChunkPos

namespace BlockPos

/-- A position is determined by its chunk and its place within that chunk. -/
theorem eq_iff_chunkPos_localPos {p q : BlockPos} :
    p = q ↔ p.chunkPos = q.chunkPos ∧ p.localPos = q.localPos := by
  rw [← blockAt_chunkPos_localPos p, ← blockAt_chunkPos_localPos q, ChunkPos.blockAt_inj]
  simp only [ChunkPos.chunkPos_blockAt, ChunkPos.localPos_blockAt]

/-- Every block is at some local position of exactly its own chunk. -/
theorem eq_blockAt_iff {p : BlockPos} {c : ChunkPos} {l : LocalPos} :
    p = c.blockAt l ↔ p.chunkPos = c ∧ p.localPos = l := by
  rw [eq_iff_chunkPos_localPos, ChunkPos.chunkPos_blockAt, ChunkPos.localPos_blockAt]

end BlockPos

namespace LocalPos

theorem ofIndex_index (l : LocalPos) : ofIndex l.index = l := by
  have := l.x.isLt; have := l.y.isLt; have := l.z.isLt
  ext <;> simp [ofIndex, index] <;> omega

theorem index_ofIndex (i : Fin 4096) : (ofIndex i).index = i := by
  have := i.isLt
  ext
  simp [ofIndex, index]
  omega

theorem index_inj {l l' : LocalPos} : l.index = l'.index ↔ l = l' := by
  constructor
  · intro h
    rw [← ofIndex_index l, ← ofIndex_index l', h]
  · rintro rfl
    rfl

/-- `LocalPos.all` lists every local position. -/
theorem mem_all (l : LocalPos) : l ∈ all := by
  simp only [all, List.mem_map]
  exact ⟨l.index, List.mem_finRange _, ofIndex_index l⟩

end LocalPos

namespace Dir

theorem mem_all (d : Dir) : d ∈ all := by
  cases d <;> simp [all]

end Dir

end LeanMc
