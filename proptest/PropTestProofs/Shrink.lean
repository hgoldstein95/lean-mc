import PropTestProofs.Game
import PropTest.Shrink

/-!
# The shrinkers are decreasing

basalt has laws for generators and none for shrinkers, so what a shrinker
should satisfy is a choice. The law proved here, of every shrinker in
`PropTest.Shrink`, is that it is **decreasing**: every candidate it offers is
strictly smaller than its input under an explicit measure, a natural number.

That is what makes "keep taking the first candidate that still fails" stop.
`Decreasing.steps_le` says how soon: a chain of shrink steps from `x` is no
longer than the size of `x`. So the cap on steps in `minimise` is a budget of
time, never what stands between it and a loop.

The last section looks at a second law, that a shrinker is **closed** under
its generator's predicate, and shows why it is not asked for: it holds of the
command shrinker and is false of the frame shrinker.
-/

open LeanMc PropTest

namespace PropTest

/-! ## Decreasing shrinkers stop -/

/-- Every candidate `shrink` offers is strictly smaller under `size`. -/
def Decreasing {α : Type} (shrink : α → List α) (size : α → Nat) : Prop :=
  ∀ x, ∀ y ∈ shrink x, size y < size x

/-- `y` is reached from `x` by `n` shrink steps, each to one of the candidates offered. -/
inductive ShrinksTo {α : Type} (shrink : α → List α) : Nat → α → α → Prop
  | refl (x : α) : ShrinksTo shrink 0 x x
  | step {n : Nat} {x y z : α} : y ∈ shrink x → ShrinksTo shrink n y z → ShrinksTo shrink (n + 1) x z

/--
**Shrinking with a decreasing shrinker stops.** A chain of shrink steps from
`x` is at most `size x` long, and shorter by the size of where it ends.
-/
theorem Decreasing.steps_le {α : Type} {shrink : α → List α} {size : α → Nat}
    (hdec : Decreasing shrink size) {n : Nat} {x y : α} (h : ShrinksTo shrink n x y) :
    n + size y ≤ size x := by
  induction h with
  | refl => omega
  | step hy _ ih =>
    have := hdec _ _ hy
    omega

/-- A shrinker that offers nothing is decreasing under any measure. -/
theorem decreasing_nil {α : Type} (size : α → Nat) : Decreasing (fun _ : α => []) size :=
  fun _ _ h => by cases h

/-! ## Numbers, vectors, inputs and commands -/

theorem shrinkNat_lt {n m : Nat} (h : m ∈ shrinkNat n) : m < n :=
  of_decide_eq_true (List.mem_filter.mp (List.mem_eraseDups.mp h)).2

theorem shrinkElapsed_lt {n m : Nat} (h : m ∈ shrinkElapsed n) : m < n :=
  of_decide_eq_true (List.mem_filter.mp (List.mem_eraseDups.mp h)).2

/-- A shrunk integer is nearer zero, on the same side of it. -/
theorem shrinkInt_between {n m : Int} (h : m ∈ shrinkInt n) :
    (0 ≤ n → 0 ≤ m ∧ m < n) ∧ (n ≤ 0 → n < m ∧ m ≤ 0) := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
  have := shrinkNat_lt hk
  simp only [Int.ofNat_eq_natCast]
  split <;> omega

theorem shrinkInt_natAbs_lt {n m : Int} (h : m ∈ shrinkInt n) : m.natAbs < n.natAbs := by
  have := shrinkInt_between h
  omega

/-- The size of a vector for shrinking: how far its components are from zero, in all. -/
def vecSize (v : Vec3) : Nat :=
  v.x.natAbs + v.y.natAbs + v.z.natAbs

theorem shrinkVec3_lt {v w : Vec3} (h : w ∈ shrinkVec3 v) : vecSize w < vecSize v := by
  simp only [shrinkVec3, List.mem_append, List.mem_map] at h
  rcases h with ((h | ⟨x, hx, rfl⟩) | ⟨y, hy, rfl⟩) | ⟨z, hz, rfl⟩
  · split at h
    · cases h
    · next hne =>
      simp only [List.mem_singleton] at h
      subst h
      have : v.x ≠ 0 ∨ v.y ≠ 0 ∨ v.z ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hne (Vec3.ext hc.1 hc.2.1 hc.2.2)
      simp only [vecSize]
      omega
  · have := shrinkInt_natAbs_lt hx
    simp only [vecSize]
    omega
  · have := shrinkInt_natAbs_lt hy
    simp only [vecSize]
    omega
  · have := shrinkInt_natAbs_lt hz
    simp only [vecSize]
    omega

def selectSize : Option (Fin 9) → Nat
  | none => 0
  | some i => i.val + 1

theorem shrinkSelect_lt {s t : Option (Fin 9)} (h : t ∈ shrinkSelect s) :
    selectSize t < selectSize s := by
  cases s with
  | none => cases h
  | some i =>
    simp only [shrinkSelect, List.mem_cons] at h
    rcases h with rfl | h
    · simp [selectSize]
    · split at h
      · cases h
      · next hi =>
        simp only [List.mem_singleton] at h
        subst h
        have : i.val ≠ 0 := fun e => hi (Fin.ext e)
        simp only [selectSize, Fin.val_zero]
        omega

def inputSize (i : Input) : Nat :=
  i.toggleFly.toNat + i.jump.toNat + i.descend.toNat + i.wishX.natAbs + i.wishZ.natAbs

theorem shrinkInput_lt {i j : Input} (h : j ∈ shrinkInput i) : inputSize j < inputSize i := by
  simp only [shrinkInput, List.mem_append, List.mem_map] at h
  rcases h with (((h | h) | h) | ⟨x, hx, rfl⟩) | ⟨z, hz, rfl⟩
  · split at h
    · next ht =>
      simp only [List.mem_singleton] at h
      subst h
      simp [inputSize, ht]
    · cases h
  · split at h
    · next ht =>
      simp only [List.mem_singleton] at h
      subst h
      simp [inputSize, ht]
    · cases h
  · split at h
    · next ht =>
      simp only [List.mem_singleton] at h
      subst h
      simp [inputSize, ht]
    · cases h
  · have := shrinkInt_natAbs_lt hx
    simp only [inputSize]
    omega
  · have := shrinkInt_natAbs_lt hz
    simp only [inputSize]
    omega

def commandSize (c : Command) : Nat :=
  c.action.isSome.toNat + selectSize c.select + inputSize c.move + vecSize c.look

/--
**The command shrinker is decreasing.** Every candidate it offers is strictly
smaller, so shrinking a command stops, after at most `commandSize c` steps.
-/
theorem shrinkCommand_lt {c d : Command} (h : d ∈ shrinkCommand c) :
    commandSize d < commandSize c := by
  simp only [shrinkCommand, List.mem_append, List.mem_map] at h
  rcases h with ((h | ⟨s, hs, rfl⟩) | ⟨m, hm, rfl⟩) | ⟨l, hl, rfl⟩
  · split at h
    · next ha =>
      simp only [List.mem_singleton] at h
      subst h
      simp [commandSize, ha]
    · cases h
  · have := shrinkSelect_lt hs
    simp only [commandSize]
    omega
  · have := shrinkInput_lt hm
    simp only [commandSize]
    omega
  · have := shrinkVec3_lt hl
    simp only [commandSize]
    omega

/-! ## Frames -/

def frameSize (f : Frame) : Nat :=
  f.dig.toNat + f.fly.toNat + f.place.toNat + selectSize f.select + f.elapsed
    + inputSize f.move + vecSize f.look

theorem shrinkFrame_lt {f g : Frame} (h : g ∈ shrinkFrame f) : frameSize g < frameSize f := by
  simp only [shrinkFrame, List.mem_append, List.mem_map] at h
  rcases h with (((((h | h) | h) | ⟨s, hs, rfl⟩) | ⟨e, he, rfl⟩) | ⟨m, hm, rfl⟩) | ⟨l, hl, rfl⟩
  · split at h
    · next ht =>
      simp only [List.mem_singleton] at h
      subst h
      simp [frameSize, ht]
    · cases h
  · split at h
    · next ht =>
      simp only [List.mem_singleton] at h
      subst h
      simp [frameSize, ht]
    · cases h
  · split at h
    · next ht =>
      simp only [List.mem_singleton] at h
      subst h
      simp [frameSize, ht]
    · cases h
  · have := shrinkSelect_lt hs
    simp only [frameSize]
    omega
  · have := shrinkElapsed_lt he
    simp only [frameSize]
    omega
  · have := shrinkInput_lt hm
    simp only [frameSize]
    omega
  · have := shrinkVec3_lt hl
    simp only [frameSize]
    omega

/-! ## Lists and pairs -/

/-- The size of a list for shrinking: the sizes of its elements, and one more for each. -/
def listSize {α : Type} (size : α → Nat) (xs : List α) : Nat :=
  (xs.map (size · + 1)).sum

theorem listSize_append {α : Type} (size : α → Nat) (xs ys : List α) :
    listSize size (xs ++ ys) = listSize size xs + listSize size ys := by
  simp [listSize]

theorem listSize_drop_le {α : Type} (size : α → Nat) (xs : List α) (j : Nat) :
    listSize size (xs.drop j) ≤ listSize size xs := by
  induction xs generalizing j with
  | nil => simp
  | cons x xs ih =>
    cases j with
    | zero => simp
    | succ j =>
      have := ih j
      simp only [List.drop_succ_cons, listSize, List.map_cons, List.sum_cons] at this ⊢
      omega

/-- Dropping at least one element from a list that has any makes it smaller. -/
theorem listSize_drop_lt {α : Type} (size : α → Nat) {xs : List α} {j : Nat} (hj : 0 < j)
    (hxs : xs ≠ []) : listSize size (xs.drop j) < listSize size xs := by
  cases xs with
  | nil => exact absurd rfl hxs
  | cons x xs =>
    cases j with
    | zero => omega
    | succ j =>
      have := listSize_drop_le size xs j
      simp only [List.drop_succ_cons, listSize, List.map_cons, List.sum_cons] at this ⊢
      omega

/-- Replacing one element by a smaller one makes the list smaller. -/
theorem listSize_set_lt {α : Type} (size : α → Nat) {xs : List α} {i : Nat} {x y : α}
    (hx : xs[i]? = some x) (hy : size y < size x) :
    listSize size (xs.set i y) < listSize size xs := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hx
  have := LeanMc.sum_map_set (size · + 1) xs i hi y
  simp only [listSize]
  omega

/--
**The list shrinker is decreasing** whenever the shrinker for its elements
is: cutting a stretch out of a list removes at least one element, and
shrinking one element in place makes that element smaller.
-/
theorem shrinkList_lt {α : Type} {sh : α → List α} {size : α → Nat} (hdec : Decreasing sh size)
    {xs ys : List α} (h : ys ∈ shrinkList sh xs) : listSize size ys < listSize size xs := by
  simp only [shrinkList, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at h
  rcases h with ⟨k, hk, i, hi, rfl⟩ | ⟨i, -, h⟩
  · obtain ⟨hk0, hkn⟩ : 0 < k ∧ k ≤ xs.length := by
      simpa using (List.mem_filter.mp (List.mem_eraseDups.mp hk)).2
    have hmul : (i + 1) * k ≤ xs.length + k - 1 := (Nat.le_div_iff_mul_le hk0).mp hi
    have hik : i * k < xs.length := by
      rw [Nat.succ_mul] at hmul
      omega
    have hne : xs.drop (i * k) ≠ [] := by
      simp only [ne_eq, List.drop_eq_nil_iff, Nat.not_le]
      exact hik
    have hdrop : xs.drop ((i + 1) * k) = (xs.drop (i * k)).drop k := by
      rw [List.drop_drop, Nat.succ_mul]
    have hlt := listSize_drop_lt size hk0 hne
    have hsplit : listSize size xs
        = listSize size (xs.take (i * k)) + listSize size (xs.drop (i * k)) := by
      rw [← listSize_append, List.take_append_drop]
    rw [listSize_append, hdrop, hsplit]
    omega
  · split at h
    · next x hx =>
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
      exact listSize_set_lt size hx (hdec x y hy)
    · cases h

theorem shrinkList_decreasing {α : Type} {sh : α → List α} {size : α → Nat}
    (hdec : Decreasing sh size) : Decreasing (shrinkList sh) (listSize size) :=
  fun _ _ h => shrinkList_lt hdec h

/-- **The pair shrinker is decreasing** whenever both of its shrinkers are. -/
theorem shrinkPair_decreasing {α β : Type} {sa : α → List α} {sb : β → List β}
    {sizeA : α → Nat} {sizeB : β → Nat} (ha : Decreasing sa sizeA) (hb : Decreasing sb sizeB) :
    Decreasing (shrinkPair sa sb) fun p => sizeA p.1 + sizeB p.2 := by
  intro p q h
  simp only [shrinkPair, List.mem_append, List.mem_map] at h
  rcases h with ⟨a, ha', rfl⟩ | ⟨b, hb', rfl⟩
  · have := ha _ _ ha'
    dsimp only
    omega
  · have := hb _ _ hb'
    dsimp only
    omega

/-! ## Renderer operations -/

def blockSize (b : Block) : Nat :=
  if b = .stone then 0 else 1

theorem shrinkBlock_lt {b c : Block} (h : c ∈ shrinkBlock b) : blockSize c < blockSize b := by
  simp only [shrinkBlock] at h
  split at h
  · cases h
  · next hb =>
    simp only [List.mem_singleton] at h
    subst h
    simp [blockSize, hb]

def chunkSize (c : ChunkPos) : Nat :=
  c.x.natAbs + c.y.natAbs + c.z.natAbs

theorem shrinkChunk_lt {c d : ChunkPos} (h : d ∈ shrinkChunk c) : chunkSize d < chunkSize c := by
  simp only [shrinkChunk, List.mem_append, List.mem_map] at h
  rcases h with ((h | ⟨x, hx, rfl⟩) | ⟨y, hy, rfl⟩) | ⟨z, hz, rfl⟩
  · split at h
    · cases h
    · next hne =>
      simp only [List.mem_singleton] at h
      subst h
      have : c.x ≠ 0 ∨ c.y ≠ 0 ∨ c.z ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hne (ChunkPos.ext hc.1 hc.2.1 hc.2.2)
      simp only [chunkSize]
      omega
  · have := shrinkInt_natAbs_lt hx
    simp only [chunkSize]
    omega
  · have := shrinkInt_natAbs_lt hy
    simp only [chunkSize]
    omega
  · have := shrinkInt_natAbs_lt hz
    simp only [chunkSize]
    omega

/-- An edit's height counts by how far it is above zero: heights shrink towards the floor, not through it. -/
def renderOpSize : RenderOp → Nat
  | .mesh c => chunkSize c
  | .edit p b => p.x.natAbs + p.y.toNat + p.z.natAbs + blockSize b
  | .dropFar c => chunkSize c
  | .draw eye => vecSize eye

theorem shrinkRenderOp_lt {op op' : RenderOp} (h : op' ∈ shrinkRenderOp op) :
    renderOpSize op' < renderOpSize op := by
  cases op with
  | mesh c =>
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
    exact shrinkChunk_lt hd
  | dropFar c =>
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
    exact shrinkChunk_lt hd
  | draw eye =>
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
    exact shrinkVec3_lt hw
  | edit p b =>
    simp only [shrinkRenderOp, List.mem_append, List.mem_map, List.mem_filterMap] at h
    rcases h with ((⟨c, hc, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨z, hz, rfl⟩) | ⟨y, hy, h⟩
    · have := shrinkBlock_lt hc
      simp only [renderOpSize]
      omega
    · have := shrinkInt_natAbs_lt hx
      simp only [renderOpSize]
      omega
    · have := shrinkInt_natAbs_lt hz
      simp only [renderOpSize]
      omega
    · have := shrinkNat_lt hy
      split at h
      · cases h
      · simp only [Option.some.injEq] at h
        subst h
        simp only [renderOpSize, Int.toNat_natCast]
        omega

/-! ## Commands to the shim -/

/-- A mesh is smaller if it is shorter, or the same length and all zeros. -/
def meshSize (v : ByteArray) : Nat :=
  2 * v.size + (if v.data.all (· == 0) then 0 else 1)

theorem shrinkMesh_lt {v w : ByteArray} (h : w ∈ shrinkMesh v) : meshSize w < meshSize v := by
  simp only [shrinkMesh, List.mem_append, List.mem_map] at h
  rcases h with ⟨n, hn, rfl⟩ | h
  · have hlt : n < v.size := of_decide_eq_true (List.mem_filter.mp (List.mem_eraseDups.mp hn)).2
    have hsize : (v.extract 0 n).size = n := by
      rw [ByteArray.size_extract]
      omega
    simp only [meshSize, hsize]
    split <;> split <;> omega
  · split at h
    · cases h
    · next hnz =>
      simp only [List.mem_singleton] at h
      subst h
      have hall : (Array.map (fun _ => (0 : UInt8)) v.data).all (· == 0) = true := by
        rw [Array.all_eq_true_iff_forall_mem]
        intro x hx
        obtain ⟨_, _, rfl⟩ := Array.mem_map.mp hx
        rfl
      have hw : meshSize ⟨Array.map (fun _ => (0 : UInt8)) v.data⟩ = 2 * v.size := by
        simp only [meshSize]
        simp only [hall, ↓reduceIte]
        simp only [ByteArray.size, Array.size_map, Nat.add_zero]
      have hv : meshSize v = 2 * v.size + 1 := by
        simp only [meshSize, hnz]
        rfl
      omega

def gpuCmdSize : GpuCmd → Nat
  | .upload slot vertices => slot + meshSize vertices
  | .unload slot => slot
  | .beginScene => 0
  | .draw slot offset => slot + vecSize offset

theorem shrinkGpuCmd_lt {cmd cmd' : GpuCmd} (h : cmd' ∈ shrinkGpuCmd cmd) :
    gpuCmdSize cmd' < gpuCmdSize cmd := by
  cases cmd with
  | beginScene => cases h
  | unload slot =>
    simp only [shrinkGpuCmd, List.mem_filterMap] at h
    obtain ⟨s, hs, h⟩ := h
    have := shrinkNat_lt hs
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      simpa [gpuCmdSize] using this
  | upload slot v =>
    simp only [shrinkGpuCmd, List.mem_append, List.mem_filterMap, List.mem_map] at h
    rcases h with ⟨s, hs, h⟩ | ⟨w, hw, rfl⟩
    · have := shrinkNat_lt hs
      split at h
      · cases h
      · simp only [Option.some.injEq] at h
        subst h
        simp only [gpuCmdSize]
        omega
    · have := shrinkMesh_lt hw
      simp only [gpuCmdSize]
      omega
  | draw slot offset =>
    simp only [shrinkGpuCmd, List.mem_append, List.mem_filterMap, List.mem_map] at h
    rcases h with ⟨s, hs, h⟩ | ⟨w, hw, rfl⟩
    · have := shrinkNat_lt hs
      split at h
      · cases h
      · simp only [Option.some.injEq] at h
        subst h
        simp only [gpuCmdSize]
        omega
    · have := shrinkVec3_lt hw
      simp only [gpuCmdSize]
      omega

/-! ## Saved games -/

def slotSize : Option Stack → Nat
  | none => 0
  | some s => 1 + s.extra.val + blockSize s.block

def inventorySize (inv : Inventory) : Nat :=
  (inv.slots.toList.map slotSize).sum

/-- Replacing one slot by a smaller one makes the inventory smaller. -/
theorem inventorySize_set_lt (inv : Inventory) (i : Fin 9) {v : Option Stack}
    (hv : slotSize v < slotSize inv.slots[i]) :
    inventorySize ⟨inv.slots.set i v⟩ < inventorySize inv := by
  have h := LeanMc.sum_map_set slotSize inv.slots.toList i.val (by simp) v
  simp only [inventorySize, Vector.toList_set]
  simp only [Vector.getElem_toList] at h
  have hget : inv.slots[i.val] = inv.slots[i] := rfl
  rw [hget] at h
  omega

theorem shrinkInventory_lt {inv inv' : Inventory} (h : inv' ∈ shrinkInventory inv) :
    inventorySize inv' < inventorySize inv := by
  simp only [shrinkInventory, List.mem_flatMap] at h
  obtain ⟨i, -, h⟩ := h
  split at h
  · cases h
  · next s hs =>
    simp only [List.mem_append, List.mem_singleton] at h
    rcases h with (rfl | h) | h
    · exact inventorySize_set_lt inv i (by rw [hs]; simp [slotSize])
    · split at h
      · cases h
      · next he =>
        simp only [List.mem_singleton] at h
        subst h
        exact inventorySize_set_lt inv i (by rw [hs]; simp only [slotSize, Fin.val_zero]; omega)
    · split at h
      · cases h
      · next hb =>
        simp only [List.mem_singleton] at h
        subst h
        exact inventorySize_set_lt inv i (by rw [hs]; simp [slotSize, blockSize, hb])

def playerSize (p : Player) : Nat :=
  vecSize p.pos + vecSize p.vel + p.onGround.toNat + p.flying.toNat

theorem shrinkPlayer_lt {p q : Player} (h : q ∈ shrinkPlayer p) : playerSize q < playerSize p := by
  simp only [shrinkPlayer, List.mem_append, List.mem_map] at h
  rcases h with ((⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩) | h) | h
  · have := shrinkVec3_lt hv
    simp only [playerSize]
    omega
  · have := shrinkVec3_lt hv
    simp only [playerSize]
    omega
  · split at h
    · next ht =>
      simp only [List.mem_singleton] at h
      subst h
      simp [playerSize, ht]
    · cases h
  · split at h
    · next ht =>
      simp only [List.mem_singleton] at h
      subst h
      simp [playerSize, ht]
    · cases h

def entitySize (e : Entity) : Nat :=
  vecSize e.pos + vecSize e.vel + e.onGround.toNat + e.walking.toNat + e.timer + e.heading.val

theorem shrinkEntity_lt {e e' : Entity} (h : e' ∈ shrinkEntity e) :
    entitySize e' < entitySize e := by
  simp only [shrinkEntity, List.mem_append, List.mem_map] at h
  rcases h with ((((⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩) | h) | h) | ⟨n, hn, rfl⟩) | h
  · have := shrinkVec3_lt hv
    simp only [entitySize]
    omega
  · have := shrinkVec3_lt hv
    simp only [entitySize]
    omega
  · split at h
    · next ht =>
      simp only [List.mem_singleton] at h
      subst h
      simp [entitySize, ht]
    · cases h
  · split at h
    · next ht =>
      simp only [List.mem_singleton] at h
      subst h
      simp [entitySize, ht]
    · cases h
  · have := shrinkNat_lt hn
    simp only [entitySize]
    omega
  · split at h
    · cases h
    · next hh =>
      simp only [List.mem_singleton] at h
      subst h
      have : e.heading.val ≠ 0 := fun eq => hh (Fin.ext eq)
      simp only [entitySize, Fin.val_zero]
      omega

def editSize (e : BlockPos × Block) : Nat :=
  e.1.x.natAbs + e.1.y.natAbs + e.1.z.natAbs + blockSize e.2

theorem shrinkEdit_lt {e e' : BlockPos × Block} (h : e' ∈ shrinkEdit e) :
    editSize e' < editSize e := by
  simp only [shrinkEdit, List.mem_append, List.mem_map] at h
  rcases h with ((⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩) | ⟨z, hz, rfl⟩) | ⟨b, hb, rfl⟩
  · have := shrinkInt_natAbs_lt hx
    simp only [editSize]
    omega
  · have := shrinkInt_natAbs_lt hy
    simp only [editSize]
    omega
  · have := shrinkInt_natAbs_lt hz
    simp only [editSize]
    omega
  · have := shrinkBlock_lt hb
    simp only [editSize]
    omega

def columnSize (c : Int × Int) : Nat :=
  c.1.natAbs + c.2.natAbs

theorem shrinkColumn_lt {c c' : Int × Int} (h : c' ∈ shrinkPair shrinkInt shrinkInt c) :
    columnSize c' < columnSize c := by
  simp only [shrinkPair, List.mem_append, List.mem_map] at h
  rcases h with ⟨x, hx, rfl⟩ | ⟨z, hz, rfl⟩
  · have := shrinkInt_natAbs_lt hx
    simp only [columnSize]
    omega
  · have := shrinkInt_natAbs_lt hz
    simp only [columnSize]
    omega

def saveSize (d : SaveData) : Nat :=
  listSize editSize d.edits + inventorySize d.inventory + playerSize d.player + d.seed.toNat
    + d.selected.val + listSize entitySize d.entities + d.rng.state.toNat
    + listSize columnSize d.populated

theorem shrinkSaveData_lt {d d' : SaveData} (h : d' ∈ shrinkSaveData d) :
    saveSize d' < saveSize d := by
  simp only [shrinkSaveData, List.mem_append, List.mem_map] at h
  rcases h with ((((((⟨es, hes, rfl⟩ | ⟨inv, hinv, rfl⟩) | ⟨p, hp, rfl⟩) | ⟨n, hn, rfl⟩) | h)
    | ⟨es, hes, rfl⟩) | ⟨n, hn, rfl⟩) | ⟨cs, hcs, rfl⟩
  · have := shrinkList_lt (fun _ _ => shrinkEdit_lt) hes
    simp only [saveSize]
    omega
  · have := shrinkInventory_lt hinv
    simp only [saveSize]
    omega
  · have := shrinkPlayer_lt hp
    simp only [saveSize]
    omega
  · have hlt := shrinkNat_lt hn
    have hbound := d.seed.toNat_lt
    have hn' : n.toUInt64.toNat = n := by
      simp only [Nat.toUInt64, UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    simp only [saveSize, hn']
    omega
  · split at h
    · cases h
    · next hsel =>
      simp only [List.mem_singleton] at h
      subst h
      have : d.selected.val ≠ 0 := fun e => hsel (Fin.ext e)
      simp only [saveSize, Fin.val_zero]
      omega
  · have := shrinkList_lt (fun _ _ => shrinkEntity_lt) hes
    simp only [saveSize]
    omega
  · have hlt := shrinkNat_lt hn
    have hbound := d.rng.state.toNat_lt
    have hn' : n.toUInt64.toNat = n := by
      simp only [Nat.toUInt64, UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    simp only [saveSize, hn']
    omega
  · have := shrinkList_lt (fun _ _ => shrinkColumn_lt) hcs
    simp only [saveSize]
    omega

/-! ## Every shrinker the tests use

Each property in `Props.lean` and `Native.lean` hands `minimise` one of these
shrinkers. Each is decreasing, so each shrinking run stops by itself.
-/

/-- Runs of commands. -/
theorem shrinkCommands_decreasing :
    Decreasing (shrinkList shrinkCommand) (listSize commandSize) :=
  shrinkList_decreasing fun _ _ => shrinkCommand_lt

/-- A seed, which is not shrunk, with a run of commands. -/
theorem shrinkSeededCommands_decreasing :
    Decreasing (shrinkPair (fun _ : UInt64 => []) (shrinkList shrinkCommand))
      fun p => 0 + listSize commandSize p.2 :=
  shrinkPair_decreasing (decreasing_nil fun _ => 0) shrinkCommands_decreasing

/-- Runs of frames. -/
theorem shrinkFrames_decreasing : Decreasing (shrinkList shrinkFrame) (listSize frameSize) :=
  shrinkList_decreasing fun _ _ => shrinkFrame_lt

/-- Rays: an origin and a direction. -/
theorem shrinkRay_decreasing :
    Decreasing (shrinkPair shrinkVec3 shrinkVec3) fun r => vecSize r.1 + vecSize r.2 :=
  shrinkPair_decreasing (fun _ _ => shrinkVec3_lt) (fun _ _ => shrinkVec3_lt)

/-- Runs of renderer operations. -/
theorem shrinkRenderOps_decreasing :
    Decreasing (shrinkList shrinkRenderOp) (listSize renderOpSize) :=
  shrinkList_decreasing fun _ _ => shrinkRenderOp_lt

/-- Saved games. -/
theorem shrinkSaveData_decreasing : Decreasing shrinkSaveData saveSize :=
  fun _ _ => shrinkSaveData_lt

/-- The integers of a save with one of them changed. -/
theorem shrinkInts_decreasing : Decreasing (shrinkList shrinkInt) (listSize Int.natAbs) :=
  shrinkList_decreasing fun _ _ => shrinkInt_natAbs_lt

/-- Bytes for the shim to decode. -/
theorem shrinkMesh_decreasing : Decreasing shrinkMesh meshSize :=
  fun _ _ => shrinkMesh_lt

/-- Runs of commands to the shim. -/
theorem shrinkGpuCmds_decreasing : Decreasing (shrinkList shrinkGpuCmd) (listSize gpuCmdSize) :=
  shrinkList_decreasing fun _ _ => shrinkGpuCmd_lt

/-- What a client is put through: renderer operations and frames. -/
theorem shrinkClientRun_decreasing :
    Decreasing (shrinkPair (shrinkList shrinkRenderOp) (shrinkList shrinkFrame))
      fun p => listSize renderOpSize p.1 + listSize frameSize p.2 :=
  shrinkPair_decreasing shrinkRenderOps_decreasing shrinkFrames_decreasing

/-- Long scenes for the shim: the number of draws, and the commands after them. -/
theorem shrinkLongScene_decreasing :
    Decreasing (shrinkPair shrinkNat (shrinkList shrinkGpuCmd))
      fun p => p.1 + listSize gpuCmdSize p.2 :=
  shrinkPair_decreasing (fun _ _ => shrinkNat_lt) shrinkGpuCmds_decreasing

/-! ## Closed: a law not asked for

A shrinker is closed if every candidate is still a value its generator could
have produced. A property that assumed its generator's predicate would need
that to trust a shrunk counterexample. None here does: each restates a theorem
about every input, so a counterexample outside the generator's reach is still
one. It holds of the command shrinker, because every range it draws from
contains zero, and fails of the frame shrinker, which shrinks into a gap the
generator leaves on purpose. The ray, renderer, shim and save shrinkers fail
it the same way.
-/

/-- Shrinking a vector inside a cube about the origin leaves it inside the cube. -/
theorem shrinkVec3_cube {r : Int} {v w : Vec3} (hv : Spec.Cube r v) (h : w ∈ shrinkVec3 v) :
    Spec.Cube r w := by
  simp only [Spec.Cube, Spec.Within] at hv ⊢
  simp only [shrinkVec3, List.mem_append, List.mem_map] at h
  rcases h with ((h | ⟨x, hx, rfl⟩) | ⟨y, hy, rfl⟩) | ⟨z, hz, rfl⟩
  · split at h
    · cases h
    · simp only [List.mem_singleton] at h
      subst h
      dsimp only
      omega
  · have := shrinkInt_between hx
    dsimp only
    omega
  · have := shrinkInt_between hy
    dsimp only
    omega
  · have := shrinkInt_between hz
    dsimp only
    omega

theorem shrinkInput_ok {i j : Input} (hi : Spec.InputOK i) (h : j ∈ shrinkInput i) :
    Spec.InputOK j := by
  simp only [Spec.InputOK, Spec.Speed, Spec.Within] at hi ⊢
  simp only [shrinkInput, List.mem_append, List.mem_map] at h
  rcases h with (((h | h) | h) | ⟨x, hx, rfl⟩) | ⟨z, hz, rfl⟩
  · split at h
    · simp only [List.mem_singleton] at h
      subst h
      exact hi
    · cases h
  · split at h
    · simp only [List.mem_singleton] at h
      subst h
      exact hi
    · cases h
  · split at h
    · simp only [List.mem_singleton] at h
      subst h
      exact hi
    · cases h
  · have := shrinkInt_between hx
    dsimp only
    omega
  · have := shrinkInt_between hz
    dsimp only
    omega

/--
**The command shrinker is closed.** Shrinking a command the generator can
produce gives only commands the generator can produce.
-/
theorem shrinkCommand_ok {c d : Command} (hc : Spec.CommandOK c) (h : d ∈ shrinkCommand c) :
    Spec.CommandOK d := by
  simp only [shrinkCommand, List.mem_append, List.mem_map] at h
  rcases h with ((h | ⟨s, hs, rfl⟩) | ⟨m, hm, rfl⟩) | ⟨l, hl, rfl⟩
  · split at h
    · simp only [List.mem_singleton] at h
      subst h
      exact hc
    · cases h
  · exact hc
  · exact ⟨shrinkInput_ok hc.1 hm, hc.2⟩
  · exact ⟨hc.1, shrinkVec3_cube hc.2 hl⟩

/-- So a shrunk command is one the command generator could have drawn. -/
theorem shrinkCommand_support {c d : Command} (hc : c ∈ SPMF.support genCommand)
    (h : d ∈ shrinkCommand c) : d ∈ SPMF.support genCommand :=
  genCommand.sound_complete.complete _ (shrinkCommand_ok (genCommand.sound_complete.sound _ hc) h)

/--
**The frame shrinker is not closed.** A frame time of 900 units, which the
generator can produce, shrinks to 899, which it cannot: the generator leaves a
gap between half a tick and nine tenths of one, and shrinking walks into it.
-/
theorem shrinkElapsed_not_closed :
    Spec.ElapsedOK 900 ∧ 899 ∈ shrinkElapsed 900 ∧ ¬ Spec.ElapsedOK 899 := by
  decide

end PropTest
