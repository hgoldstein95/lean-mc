import LeanMc.Core.View
import LeanMc.Proofs.Mesh
import LeanMc.Proofs.Player

/-!
# View theorems

* **Streaming covers the view.** The offsets the renderer walks reach exactly
  the chunks in view, so no chunk in view is left unloaded.
* **Nothing in view is dropped.** A chunk in view is never counted as far away,
  whatever slack is allowed, so loading and unloading cannot fight.
* **The rebuild list is complete.** A block change leaves the mesh of every
  chunk outside `dirtyChunks` exactly as it was.
-/

namespace LeanMc

namespace ViewRange

theorem mem_offsets {v : ViewRange} {o : Int × Int × Int} :
    o ∈ v.offsets ↔
      o.1.natAbs ≤ v.radius ∧ o.2.1.natAbs ≤ v.radiusY ∧ o.2.2.natAbs ≤ v.radius := by
  obtain ⟨dx, dy, dz⟩ := o
  simp only [offsets, List.mem_flatMap, List.mem_map, mem_intRange, Prod.mk.injEq]
  constructor
  · rintro ⟨x, hx, y, hy, z, hz, rfl, rfl, rfl⟩
    omega
  · intro h
    exact ⟨dx, by omega, dy, by omega, dz, by omega, rfl, rfl, rfl⟩

/-- **Streaming covers the view**: a chunk is in view exactly when some offset reaches it. -/
theorem contains_iff_offset {v : ViewRange} {centre c : ChunkPos} :
    v.contains centre c = true ↔ ∃ o ∈ v.offsets, offsetChunk centre o = c := by
  simp only [contains, Bool.and_eq_true, decide_eq_true_eq, Nat.add_zero]
  constructor
  · intro h
    refine ⟨(c.x - centre.x, c.y - centre.y, c.z - centre.z), mem_offsets.mpr ?_, ?_⟩
    · exact ⟨h.1.1, h.1.2, h.2⟩
    · ext <;> simp [offsetChunk] <;> omega
  · rintro ⟨o, ho, rfl⟩
    have := mem_offsets.mp ho
    simp only [offsetChunk]
    omega

/-- **Nothing in view is dropped**, whatever slack the unloading rule is given. -/
theorem not_isFar_of_contains {v : ViewRange} {centre c : ChunkPos}
    (h : v.contains centre c = true) (slack : Nat) : v.isFar centre c slack = false := by
  simp only [isFar, contains, Bool.and_eq_true, decide_eq_true_eq, Nat.add_zero,
    Bool.not_eq_false'] at h ⊢
  omega

end ViewRange

theorem mem_dirtyChunks {p : BlockPos} {c : ChunkPos} :
    c ∈ dirtyChunks p ↔ c = p.chunkPos ∨ ∃ d, c = (p.step d).chunkPos := by
  simp only [dirtyChunks, List.mem_eraseDups, List.mem_cons, List.mem_map]
  constructor
  · rintro (h | ⟨d, -, rfl⟩)
    · exact .inl h
    · exact .inr ⟨d, rfl⟩
  · rintro (h | ⟨d, rfl⟩)
    · exact .inl h
    · exact .inr ⟨d, Dir.mem_all d, rfl⟩

/--
**The rebuild list is complete.** After a block change, every chunk not in
`dirtyChunks` has exactly the mesh it had before.
-/
theorem meshChunk_set_of_not_dirty (w : World) (p : BlockPos) (b : Block) {c : ChunkPos}
    (h : c ∉ dirtyChunks p) : meshChunk (w.set p b).get c = meshChunk w.get c := by
  rw [mem_dirtyChunks] at h
  exact meshChunk_set w p b c (fun e => h (.inl e)) (fun d e => h (.inr ⟨d, e⟩))

end LeanMc
