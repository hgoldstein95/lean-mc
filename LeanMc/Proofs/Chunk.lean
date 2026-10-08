import LeanMc.Core.Chunk
import LeanMc.Proofs.Pos

/-!
# Chunk storage theorems

Reading and writing a chunk by local position behaves like a total map: a
write is seen at its own position and nowhere else.
-/

namespace LeanMc.Chunk

theorem get_set_self (c : Chunk) (l : LocalPos) (b : Block) : (c.set l b).get l = b := by
  simp [get, set]

theorem get_set_of_ne (c : Chunk) {l l' : LocalPos} (b : Block) (h : l' ≠ l) :
    (c.set l b).get l' = c.get l' := by
  have hi : l.index.val ≠ l'.index.val := fun e => h (LocalPos.index_inj.mp (Fin.ext e)).symm
  simp [get, set, hi]

theorem get_set (c : Chunk) (l l' : LocalPos) (b : Block) :
    (c.set l b).get l' = if l' = l then b else c.get l' := by
  split
  · subst_vars; exact get_set_self ..
  · exact get_set_of_ne _ _ ‹_›

theorem get_ofFn (f : LocalPos → Block) (l : LocalPos) : (ofFn f).get l = f l := by
  simp [get, ofFn, LocalPos.ofIndex_index]

/-- Chunks holding the same block at every local position are equal. -/
theorem ext_get {c c' : Chunk} (h : ∀ l, c.get l = c'.get l) : c = c' := by
  ext i hi
  have := h (LocalPos.ofIndex ⟨i, hi⟩)
  simpa [get, LocalPos.index_ofIndex] using this

end LeanMc.Chunk
