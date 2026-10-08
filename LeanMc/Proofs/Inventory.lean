import LeanMc.Core.Inventory

/-!
# Inventory theorems

* **Picking up adds exactly one.** After `add b`, the count of `b` is one more
  and every other count is unchanged.
* **Taking removes exactly one.** After `take`, the count of the block taken is
  one less and every other count is unchanged.
* **Air is never carried**, provided it is never picked up.

That a stack holds between 1 and 64 blocks needs no theorem: the type allows
nothing else.
-/

namespace LeanMc

theorem sum_map_set {α : Type} (f : α → Nat) (l : List α) (i : Nat) (h : i < l.length) (v : α) :
    ((l.set i v).map f).sum + f l[i] = (l.map f).sum + f v := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.map_cons, List.sum_cons, List.getElem_cons_zero]
      omega
    | succ i =>
      have := ih i (by simpa using h)
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ]
      omega

namespace Stack

/-- A stack is never empty and never over the limit. -/
theorem count_bounds (s : Stack) : 1 ≤ s.count ∧ s.count ≤ limit := by
  have := s.extra.isLt
  simp only [count, limit]
  omega

end Stack

namespace Inventory

theorem slotCount_put {slot : Option Stack} {b : Block} {s : Stack}
    (h : Stack.put? slot b = some s) (b' : Block) :
    slotCount b' (some s) = slotCount b' slot + (if b' = b then 1 else 0) := by
  cases slot with
  | none =>
    simp only [Stack.put?, Option.some.injEq] at h
    subst h
    by_cases hb : b' = b
    · simp [slotCount, Stack.count, hb]
    · have : ¬ b = b' := fun e => hb e.symm
      simp [slotCount, hb, this]
  | some st =>
    simp only [Stack.put?] at h
    split at h
    · next hfit =>
      cases h
      by_cases hb : b' = b
      · subst hb
        simp [slotCount, Stack.count, hfit.1]
      · have h1 : ¬ st.block = b' := fun e => hb (e ▸ hfit.1)
        have h2 : ¬ b = b' := fun e => hb e.symm
        simp [slotCount, hb, h1, h2]
    · cases h

theorem slotCount_takeOne (s : Stack) (b' : Block) :
    slotCount b' (some s) = slotCount b' s.takeOne + (if b' = s.block then 1 else 0) := by
  unfold Stack.takeOne
  by_cases hb : b' = s.block
  · subst hb
    split <;> simp [slotCount, Stack.count] <;> omega
  · have : ¬ s.block = b' := fun e => hb e.symm
    split <;> simp [slotCount, this]

theorem count_set (inv : Inventory) (i : Fin 9) (v : Option Stack) (b : Block) :
    (⟨inv.slots.set i v⟩ : Inventory).count b + slotCount b inv.slots[i]
      = inv.count b + slotCount b v := by
  have h := sum_map_set (slotCount b) inv.slots.toList i.val (by simp) v
  simpa [count, Vector.toList_set] using h

/-- **Picking up adds exactly one**, and only of the block picked up. -/
theorem count_add {inv inv' : Inventory} {b : Block} (h : inv.add b = some inv') (b' : Block) :
    inv'.count b' = inv.count b' + (if b' = b then 1 else 0) := by
  unfold add at h
  split at h
  · cases h
  · next i _ =>
    split at h
    · next stack hput =>
      cases h
      have h1 := count_set inv i (some stack) b'
      have h2 := slotCount_put hput b'
      omega
    · cases h

/-- **Taking removes exactly one**, and only of the block taken. -/
theorem count_take {inv inv' : Inventory} {i : Fin 9} {b : Block}
    (h : inv.take i = some (b, inv')) (b' : Block) :
    inv.count b' = inv'.count b' + (if b' = b then 1 else 0) := by
  unfold take at h
  split at h
  · cases h
  · next s hs =>
    cases h
    have h1 := count_set inv i s.takeOne b'
    have h2 := slotCount_takeOne s b'
    rw [hs] at h1
    omega

/-- No slot holds a stack of air. -/
def NoAir (inv : Inventory) : Prop :=
  ∀ (i : Fin 9) (s : Stack), inv.slots[i] = some s → s.block ≠ .air

theorem noAir_empty : ({} : Inventory).NoAir := by
  intro i s h
  simp at h

theorem NoAir.set {inv : Inventory} (h : inv.NoAir) (i : Fin 9) {v : Option Stack}
    (hv : ∀ s, v = some s → s.block ≠ .air) : (⟨inv.slots.set i v⟩ : Inventory).NoAir := by
  intro j s hs
  have hget : (inv.slots.set i v)[j] = if i.val = j.val then v else inv.slots[j] := by
    simp [Vector.getElem_set]
  rw [hget] at hs
  split at hs
  · exact hv s hs
  · exact h j s hs

theorem NoAir.add {inv inv' : Inventory} {b : Block} (h : inv.NoAir) (hb : b ≠ .air)
    (ha : inv.add b = some inv') : inv'.NoAir := by
  unfold Inventory.add at ha
  split at ha
  · cases ha
  · next i _ =>
    split at ha
    · next stack hput =>
      cases ha
      refine h.set i (fun s hs => ?_)
      cases hs
      cases hslot : inv.slots[i] with
      | none =>
        simp only [hslot, Stack.put?, Option.some.injEq] at hput
        rw [← hput]
        exact hb
      | some st =>
        simp only [hslot, Stack.put?] at hput
        split at hput
        · cases hput
          exact hb
        · cases hput
    · cases ha

theorem NoAir.take {inv inv' : Inventory} {i : Fin 9} {b : Block} (h : inv.NoAir)
    (ht : inv.take i = some (b, inv')) : b ≠ .air ∧ inv'.NoAir := by
  unfold Inventory.take at ht
  split at ht
  · cases ht
  · next s hs =>
    cases ht
    refine ⟨h i s hs, h.set i (fun s' hs' => ?_)⟩
    unfold Stack.takeOne at hs'
    split at hs'
    · cases hs'
    · cases hs'
      exact h i s hs

end Inventory

end LeanMc
