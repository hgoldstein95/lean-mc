import LeanMc.Core.Render
import LeanMc.Proofs.View

/-!
# Renderer theorems

Everything here is about the planner run against the `Gpu` model.

* **The planner never misuses the shim.** No command it sends is a fault: it
  never draws or empties a slot that holds nothing, and never uploads to a bad
  slot or uploads a malformed mesh.
* **Slots are never shared.** Two chunks never hold the same slot, and a slot
  on the free list is not in use.
* **What is drawn is what is there.** After any sequence of loads, edits and
  unloads, every chunk the planner counts as meshed has exactly the world's
  mesh in its slot, or nothing to draw; and a frame's scene is exactly one draw
  of each such mesh, at its chunk's position relative to the eye.

Together with the meshing theorems, the scene the model ends up with is the
visible faces of the world's loaded chunks. That the real shim behaves like the
model is checked by tests.
-/

namespace LeanMc

namespace Gpu

theorem run_append (g : Gpu) (a b : List GpuCmd) : g.run (a ++ b) = (g.run a).run b :=
  List.foldl_append ..

theorem exec_upload (g : Gpu) {slot : Nat} {v : ByteArray} (h0 : slot ≠ 0) (hc : slot < capacity)
    (hv : v.size ≠ 0) (h24 : v.size % triangleBytes = 0) :
    g.exec (.upload slot v) = { g with meshes := g.meshes.insert slot v } := by
  have : ¬ capacity ≤ slot := by omega
  simp [exec, h0, hv, h24, this]

theorem exec_unload (g : Gpu) {slot : Nat} (h : g.meshes.contains slot = true) :
    g.exec (.unload slot) = { g with meshes := g.meshes.erase slot } := by
  simp [exec, h]

end Gpu

/-! ## What the shim sees in a mesh -/

/-- The vertex the shim should see for one corner of a face. -/
def Face.gpuVertex (f : Face) (i : Fin 4) : GpuVertex where
  x := f.pos.x.val + (f.dir.corner i).1
  y := f.pos.y.val + (f.dir.corner i).2.1
  z := f.pos.z.val + (f.dir.corner i).2.2
  u := f.block.tile f.dir % 16 + (cornerUV i).1
  v := f.block.tile f.dir / 16 + (cornerUV i).2
  shade := f.dir.shade.toNat
  normal := f.dir.toNat

namespace Gpu

theorem decodeList_vertex (f : Face) (i : Fin 4) (rest : List UInt8) :
    decodeList (f.vertex i ++ rest) = f.gpuVertex i :: decodeList rest := by
  have h := Face.toNat_vertex f i
  simp only [Face.vertex, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
  obtain ⟨hx, hy, hz, hu, hv, -, hn, -⟩ := h
  have hlt := f.dir.toNat_lt
  simp only [Face.vertex, List.cons_append, List.nil_append, decodeList, hx, hy, hz, hu, hv, hn,
    hlt, ↓reduceIte, Face.gpuVertex]

theorem decodeList_bytes (f : Face) (rest : List UInt8) :
    decodeList (f.bytes ++ rest) = Face.triangleCorners.map f.gpuVertex ++ decodeList rest := by
  simp [Face.bytes, Face.triangleCorners, List.append_assoc, decodeList_vertex]

/--
**The shim sees the faces.** Read the way the shim reads it, a packed mesh is
exactly the six triangle corners of each face, in order, with no field
misread.
-/
theorem decode_packFaces (faces : List Face) :
    decode (packFaces faces) = faces.flatMap fun f => Face.triangleCorners.map f.gpuVertex := by
  rw [decode, toList_packFaces]
  induction faces with
  | nil => rfl
  | cons f fs ih => rw [List.flatMap_cons, decodeList_bytes, ih, List.flatMap_cons]

/-- For a chunk's mesh: the shim sees exactly the corners of the chunk's visible faces. -/
theorem decode_meshChunk (blockAt : BlockPos → Block) (c : ChunkPos) :
    decode (meshChunk blockAt c)
      = (chunkFaces blockAt c).flatMap fun f => Face.triangleCorners.map f.gpuVertex :=
  decode_packFaces _

end Gpu

namespace Renderer

/--
The planner and the graphics side agree with the world, except possibly about
the mesh contents of chunks marked `dirty`, which are waiting to be rebuilt.
-/
structure Synced (dirty : ChunkPos → Prop) (r : Renderer) (w : World) (g : Gpu) : Prop where
  cache : r.cache.Valid w
  noFault : g.fault = false
  /-- A meshed chunk's slot holds a mesh. -/
  live : ∀ (c : ChunkPos) (s : Nat), r.slots[c]? = some s → s ≠ 0 → g.meshes.contains s = true
  /-- A clean meshed chunk's slot holds exactly the world's mesh for it. -/
  mesh : ∀ (c : ChunkPos) (s : Nat), r.slots[c]? = some s → s ≠ 0 → ¬ dirty c →
    g.meshes[s]? = some (meshChunk w.get c)
  /-- A clean chunk recorded as having nothing to draw really has nothing to draw. -/
  empty : ∀ c : ChunkPos, r.slots[c]? = some 0 → ¬ dirty c → (meshChunk w.get c).size = 0
  /-- No two chunks share a slot. -/
  inj : ∀ (c c' : ChunkPos) (s : Nat), r.slots[c]? = some s → r.slots[c']? = some s → s ≠ 0 →
    c = c'
  bound : ∀ (c : ChunkPos) (s : Nat), r.slots[c]? = some s → s < r.next
  /-- Free slots are real slots that no chunk is using. -/
  free : ∀ s ∈ r.free, 0 < s ∧ s < r.next ∧ ∀ c : ChunkPos, r.slots[c]? ≠ some s
  freeNodup : r.free.Nodup
  next : 0 < r.next ∧ r.next ≤ Gpu.capacity

/-- Nothing loaded, nothing uploaded: trivially in agreement. -/
theorem Synced.initial (w : World) : Synced (fun _ => False) {} w {} where
  cache := ChunkCache.valid_empty w
  noFault := rfl
  live := by simp
  mesh := by simp
  empty := by simp
  inj := by simp
  bound := by simp
  free := by simp
  freeNodup := List.nodup_nil
  next := by decide

theorem Synced.mono {dirty dirty' : ChunkPos → Prop} {r : Renderer} {w : World} {g : Gpu}
    (h : Synced dirty r w g) (hd : ∀ c, dirty c → dirty' c) : Synced dirty' r w g :=
  { h with
    mesh := fun c s hs h0 hn => h.mesh c s hs h0 (fun hc => hn (hd c hc))
    empty := fun c hs hn => h.empty c hs (fun hc => hn (hd c hc)) }

/-- Dirty chunks that are not meshed need no rebuilding. -/
theorem Synced.clear {dirty : ChunkPos → Prop} {r : Renderer} {w : World} {g : Gpu}
    (h : Synced dirty r w g) (hd : ∀ c : ChunkPos, dirty c → r.slots[c]? = none) :
    Synced (fun _ => False) r w g :=
  { h with
    mesh := fun c s hs h0 _ => h.mesh c s hs h0 (fun hc => by rw [hd c hc] at hs; cases hs)
    empty := fun c hs _ => h.empty c hs (fun hc => by rw [hd c hc] at hs; cases hs) }

theorem slot_of_getD_ne_zero {r : Renderer} {c : ChunkPos} (h : r.slots[c]?.getD 0 ≠ 0) :
    r.slots[c]? = some (r.slots[c]?.getD 0) := by
  cases hc : r.slots[c]? with
  | none => simp [hc] at h
  | some s => rfl

theorem not_slot_of_getD_eq_zero {r : Renderer} {c : ChunkPos} (h : r.slots[c]?.getD 0 = 0)
    {s : Nat} (hs : r.slots[c]? = some s) : s = 0 := by
  simpa [hs] using h

/-- What taking a slot gives: a real, unused slot, with the bookkeeping still in order. -/
theorem alloc_spec {dirty : ChunkPos → Prop} {r r' : Renderer} {w : World} {g : Gpu}
    (h : Synced dirty r w g) {s : Nat} (ha : r.alloc = some (s, r')) :
    r'.cache = r.cache ∧ r'.slots = r.slots ∧ 0 < s ∧ s < r'.next
      ∧ (∀ c : ChunkPos, r.slots[c]? ≠ some s)
      ∧ (∀ (c : ChunkPos) (s' : Nat), r.slots[c]? = some s' → s' < r'.next)
      ∧ (∀ s' ∈ r'.free, 0 < s' ∧ s' < r'.next ∧ s' ≠ s ∧ ∀ c : ChunkPos, r.slots[c]? ≠ some s')
      ∧ r'.free.Nodup ∧ (0 < r'.next ∧ r'.next ≤ Gpu.capacity) := by
  unfold alloc at ha
  split at ha
  · next slot rest hfree =>
    cases ha
    have hmem : s ∈ r.free := by rw [hfree]; exact List.mem_cons_self
    have hnd := h.freeNodup
    rw [hfree, List.nodup_cons] at hnd
    obtain ⟨hpos, hlt, hun⟩ := h.free s hmem
    refine ⟨rfl, rfl, hpos, hlt, hun, h.bound, ?_, hnd.2, h.next⟩
    intro s' hs'
    obtain ⟨h1, h2, h3⟩ := h.free s' (by rw [hfree]; exact List.mem_cons_of_mem _ hs')
    exact ⟨h1, h2, fun e => hnd.1 (e ▸ hs'), h3⟩
  · next hfree =>
    split at ha
    · next hlt =>
      cases ha
      refine ⟨rfl, rfl, h.next.1, Nat.lt_succ_self _, ?_, ?_, ?_, ?_, ?_⟩
      · intro c hc
        exact Nat.lt_irrefl _ (h.bound c _ hc)
      · intro c s' hs'
        exact Nat.lt_succ_of_lt (h.bound c s' hs')
      · intro s' hs'
        simp [hfree] at hs'
      · simp [hfree]
      · exact ⟨Nat.succ_pos _, hlt⟩
    · cases ha

/--
Recording a chunk's new mesh keeps everything in agreement and makes that chunk
clean, whether the mesh is new, replaced, emptied or could not be given a slot.
-/
theorem Synced.setMesh {dirty : ChunkPos → Prop} {r : Renderer} {w : World} {g : Gpu}
    (h : Synced dirty r w g) (c : ChunkPos) {v : ByteArray} (hv : v = meshChunk w.get c) :
    Synced (fun c' => dirty c' ∧ c' ≠ c) (r.setMesh c v).1 w (g.run (r.setMesh c v).2) := by
  have h24 : v.size % Gpu.triangleBytes = 0 := by
    rw [hv, size_meshChunk, Gpu.triangleBytes]
    omega
  unfold Renderer.setMesh
  by_cases hslot : r.slots[c]?.getD 0 ≠ 0
  · -- The chunk already holds a slot.
    have hc := slot_of_getD_ne_zero hslot
    generalize r.slots[c]?.getD 0 = s at hslot hc ⊢
    have hlive := h.live c s hc hslot
    have hif : (s ≠ 0) = True := eq_true hslot
    by_cases hz : v.size = 0
    · -- Its mesh is now empty: give the slot back.
      simp only [hif, ↓reduceIte, hz, Gpu.run, List.foldl_cons, List.foldl_nil,
        Gpu.exec_unload g hlive]
      have hne : ∀ (c' : ChunkPos) (s' : Nat), (r.slots.insert c 0)[c']? = some s' → s' ≠ 0 →
          c' ≠ c ∧ r.slots[c']? = some s' := by
        intro c' s' hs' h0
        rw [Std.HashMap.getElem?_insert] at hs'
        split at hs'
        · cases hs'
          exact absurd rfl h0
        · next hcc => exact ⟨fun e => hcc (by simp [e]), hs'⟩
      have hother : ∀ (c' : ChunkPos) (s' : Nat), c' ≠ c → r.slots[c']? = some s' → s' ≠ 0 → s' ≠ s :=
        fun c' s' hcc hs' h0 e => hcc (h.inj c' c s' hs' (e ▸ hc) h0)
      refine { cache := h.cache, noFault := h.noFault, live := ?_, mesh := ?_, empty := ?_,
               inj := ?_, bound := ?_, free := ?_, freeNodup := ?_, next := h.next }
      · intro c' s' hs' h0
        obtain ⟨hcc, hold⟩ := hne c' s' hs' h0
        simp only [Std.HashMap.contains_erase, Bool.and_eq_true, Bool.not_eq_true',
          beq_eq_false_iff_ne, ne_eq]
        exact ⟨fun e => hother c' s' hcc hold h0 e.symm, h.live c' s' hold h0⟩
      · intro c' s' hs' h0 hd
        obtain ⟨hcc, hold⟩ := hne c' s' hs' h0
        rw [Std.HashMap.getElem?_erase]
        have : (s == s') = false := by simpa using fun e => hother c' s' hcc hold h0 e.symm
        simp only [this, Bool.false_eq_true, ↓reduceIte]
        exact h.mesh c' s' hold h0 (fun hdc => hd ⟨hdc, hcc⟩)
      · intro c' hs' hd
        rw [Std.HashMap.getElem?_insert] at hs'
        split at hs'
        · next hcc =>
          have : c = c' := by simpa using hcc
          rw [← this, ← hv, hz]
        · next hcc =>
          exact h.empty c' hs' (fun hdc => hd ⟨hdc, fun e => hcc (by simp [e])⟩)
      · intro c1 c2 s' h1 h2 h0
        exact h.inj c1 c2 s' (hne c1 s' h1 h0).2 (hne c2 s' h2 h0).2 h0
      · intro c' s' hs'
        rw [Std.HashMap.getElem?_insert] at hs'
        split at hs'
        · cases hs'
          exact h.next.1
        · exact h.bound c' s' hs'
      · intro s' hs'
        have hins : ∀ c' : ChunkPos, r.slots[c']? ≠ some s' → 0 < s' →
            (r.slots.insert c 0)[c']? ≠ some s' := by
          intro c' hold hpos hnew
          rw [Std.HashMap.getElem?_insert] at hnew
          split at hnew
          · cases hnew
            exact Nat.lt_irrefl _ hpos
          · exact hold hnew
        rcases List.mem_cons.mp hs' with rfl | hmem
        · refine ⟨Nat.pos_of_ne_zero hslot, h.bound c _ hc, fun c' => ?_⟩
          by_cases hcc : c' = c
          · subst hcc
            simp only [Std.HashMap.getElem?_insert_self, ne_eq, Option.some.injEq]
            exact fun e => hslot e.symm
          · exact hins c' (fun hold => hcc (h.inj c' c _ hold hc hslot)) (Nat.pos_of_ne_zero hslot)
        · obtain ⟨h1, h2, h3⟩ := h.free s' hmem
          exact ⟨h1, h2, fun c' => hins c' (h3 c') h1⟩
      · rw [List.nodup_cons]
        exact ⟨fun hmem => (h.free s hmem).2.2 c hc, h.freeNodup⟩
    · -- Its mesh changed: replace it in place.
      have hup := Gpu.exec_upload g hslot (Nat.lt_of_lt_of_le (h.bound c s hc) h.next.2) hz h24
      simp only [hif, ↓reduceIte, hz, Gpu.run, List.foldl_cons, List.foldl_nil, hup]
      refine { h with live := ?_, mesh := ?_, empty := ?_ }
      · intro c' s' hs' h0
        rw [Std.HashMap.contains_insert, h.live c' s' hs' h0]
        simp
      · intro c' s' hs' h0 hd
        rw [Std.HashMap.getElem?_insert]
        by_cases hss : s = s'
        · subst hss
          have : c' = c := h.inj c' c s hs' hc h0
          simp [this, hv]
        · have hbeq : (s == s') = false := by simpa using hss
          simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
          exact h.mesh c' s' hs' h0 (fun hdc => hd ⟨hdc, fun e => hss (by
            subst e; rw [hc] at hs'; exact Option.some.inj hs')⟩)
      · intro c' hs' hd
        exact h.empty c' hs' (fun hdc => hd ⟨hdc, fun e => hslot (by
          subst e; rw [hc] at hs'; exact Option.some.inj hs')⟩)
  · -- The chunk holds no slot yet.
    have hslot0 : r.slots[c]?.getD 0 = 0 := by simpa using hslot
    have hzero : ∀ s : Nat, r.slots[c]? = some s → s = 0 := fun s => not_slot_of_getD_eq_zero hslot0
    simp only [hslot0, ne_eq, not_true_eq_false, ↓reduceIte]
    by_cases hz : v.size = 0
    · -- Nothing to draw: just record that.
      simp only [hz, ↓reduceIte, Gpu.run, List.foldl_nil]
      have hne : ∀ (c' : ChunkPos) (s' : Nat), (r.slots.insert c 0)[c']? = some s' → s' ≠ 0 →
          c' ≠ c ∧ r.slots[c']? = some s' := by
        intro c' s' hs' h0
        rw [Std.HashMap.getElem?_insert] at hs'
        split at hs'
        · cases hs'
          exact absurd rfl h0
        · next hcc => exact ⟨fun e => hcc (by simp [e]), hs'⟩
      refine { cache := h.cache, noFault := h.noFault, live := ?_, mesh := ?_, empty := ?_,
               inj := ?_, bound := ?_, free := ?_, freeNodup := h.freeNodup, next := h.next }
      · intro c' s' hs' h0
        exact h.live c' s' (hne c' s' hs' h0).2 h0
      · intro c' s' hs' h0 hd
        obtain ⟨hcc, hold⟩ := hne c' s' hs' h0
        exact h.mesh c' s' hold h0 (fun hdc => hd ⟨hdc, hcc⟩)
      · intro c' hs' hd
        rw [Std.HashMap.getElem?_insert] at hs'
        split at hs'
        · next hcc =>
          have : c = c' := by simpa using hcc
          rw [← this, ← hv, hz]
        · next hcc =>
          exact h.empty c' hs' (fun hdc => hd ⟨hdc, fun e => hcc (by simp [e])⟩)
      · intro c1 c2 s' h1 h2 h0
        exact h.inj c1 c2 s' (hne c1 s' h1 h0).2 (hne c2 s' h2 h0).2 h0
      · intro c' s' hs'
        rw [Std.HashMap.getElem?_insert] at hs'
        split at hs'
        · cases hs'
          exact h.next.1
        · exact h.bound c' s' hs'
      · intro s' hs'
        obtain ⟨h1, h2, h3⟩ := h.free s' hs'
        refine ⟨h1, h2, fun c' hnew => ?_⟩
        rw [Std.HashMap.getElem?_insert] at hnew
        split at hnew
        · cases hnew
          exact Nat.lt_irrefl _ h1
        · exact h3 c' hnew
    · simp only [hz, ↓reduceIte]
      cases ha : r.alloc with
      | none =>
        -- No slot to be had: leave the chunk unmeshed.
        simp only [Gpu.run, List.foldl_nil]
        have hold : ∀ (c' : ChunkPos) (s' : Nat), (r.slots.erase c)[c']? = some s' →
            c' ≠ c ∧ r.slots[c']? = some s' := by
          intro c' s' hs'
          rw [Std.HashMap.getElem?_erase] at hs'
          split at hs'
          · cases hs'
          · next hcc => exact ⟨fun e => hcc (by simp [e]), hs'⟩
        refine { cache := h.cache, noFault := h.noFault, live := ?_, mesh := ?_, empty := ?_,
                 inj := ?_, bound := ?_, free := ?_, freeNodup := h.freeNodup, next := h.next }
        · exact fun c' s' hs' h0 => h.live c' s' (hold c' s' hs').2 h0
        · intro c' s' hs' h0 hd
          obtain ⟨hcc, ho⟩ := hold c' s' hs'
          exact h.mesh c' s' ho h0 (fun hdc => hd ⟨hdc, hcc⟩)
        · intro c' hs' hd
          obtain ⟨hcc, ho⟩ := hold c' 0 hs'
          exact h.empty c' ho (fun hdc => hd ⟨hdc, hcc⟩)
        · exact fun c1 c2 s' h1 h2 h0 => h.inj c1 c2 s' (hold c1 s' h1).2 (hold c2 s' h2).2 h0
        · exact fun c' s' hs' => h.bound c' s' (hold c' s' hs').2
        · intro s' hs'
          obtain ⟨h1, h2, h3⟩ := h.free s' hs'
          exact ⟨h1, h2, fun c' hnew => h3 c' (hold c' s' hnew).2⟩
      | some pair =>
        -- A slot was found: upload into it.
        obtain ⟨s, r'⟩ := pair
        obtain ⟨hcache, hslots, hpos, hlt, hunused, hbound, hfree, hnodup, hnext⟩ := alloc_spec h ha
        have hs0 : s ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
        have hup := Gpu.exec_upload g hs0 (Nat.lt_of_lt_of_le hlt hnext.2) hz h24
        simp only [Gpu.run, List.foldl_cons, List.foldl_nil, hup, hslots]
        have hcases : ∀ (c' : ChunkPos) (s' : Nat), (r.slots.insert c s)[c']? = some s' →
            (c' = c ∧ s' = s) ∨ (c' ≠ c ∧ r.slots[c']? = some s' ∧ s' ≠ s) := by
          intro c' s' hs'
          rw [Std.HashMap.getElem?_insert] at hs'
          split at hs'
          · next hcc =>
            cases hs'
            exact .inl ⟨by simpa using Eq.symm (by simpa using hcc), rfl⟩
          · next hcc =>
            exact .inr ⟨fun e => hcc (by simp [e]), hs', fun e => hunused c' (e ▸ hs')⟩
        refine { cache := hcache ▸ h.cache, noFault := h.noFault, live := ?_, mesh := ?_,
                 empty := ?_, inj := ?_, bound := ?_, free := ?_, freeNodup := hnodup,
                 next := hnext }
        · intro c' s' hs' h0
          rw [Std.HashMap.contains_insert]
          rcases hcases c' s' hs' with ⟨-, rfl⟩ | ⟨-, hold, -⟩
          · simp
          · simp [h.live c' s' hold h0]
        · intro c' s' hs' h0 hd
          rw [Std.HashMap.getElem?_insert]
          rcases hcases c' s' hs' with ⟨rfl, rfl⟩ | ⟨hcc, hold, hss⟩
          · simp [hv]
          · have hbeq : (s == s') = false := by simpa using fun e => hss e.symm
            simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
            exact h.mesh c' s' hold h0 (fun hdc => hd ⟨hdc, hcc⟩)
        · intro c' hs' hd
          rcases hcases c' 0 hs' with ⟨-, e⟩ | ⟨hcc, hold, -⟩
          · exact absurd e.symm hs0
          · exact h.empty c' hold (fun hdc => hd ⟨hdc, hcc⟩)
        · intro c1 c2 s' h1 h2 h0
          rcases hcases c1 s' h1 with ⟨rfl, rfl⟩ | ⟨-, ho1, hne1⟩
          · rcases hcases c2 s' h2 with ⟨rfl, -⟩ | ⟨-, -, hne2⟩
            · rfl
            · exact absurd rfl hne2
          · rcases hcases c2 s' h2 with ⟨-, e⟩ | ⟨-, ho2, -⟩
            · exact absurd e hne1
            · exact h.inj c1 c2 s' ho1 ho2 h0
        · intro c' s' hs'
          rcases hcases c' s' hs' with ⟨-, rfl⟩ | ⟨-, hold, -⟩
          · exact hlt
          · exact hbound c' s' hold
        · intro s' hs'
          obtain ⟨h1, h2, h3, h4⟩ := hfree s' hs'
          refine ⟨h1, h2, fun c' hnew => ?_⟩
          rcases hcases c' s' hnew with ⟨-, e⟩ | ⟨-, hold, -⟩
          · exact h3 e
          · exact h4 c' hold

/-! ## Rebuilding, dropping and editing -/

theorem loadAround_valid {cache : ChunkCache} {w : World} (h : cache.Valid w) (c : ChunkPos) :
    (loadAround cache w c).Valid w := by
  unfold loadAround
  have h0 := h.load c
  generalize cache.load w c = start at h0
  generalize Dir.all = dirs
  induction dirs generalizing start with
  | nil => exact h0
  | cons d ds ih => exact ih _ (h0.load _)

theorem Synced.withCache {dirty : ChunkPos → Prop} {r : Renderer} {w : World} {g : Gpu}
    (h : Synced dirty r w g) {cache : ChunkCache} (hc : cache.Valid w) :
    Synced dirty { r with cache } w g :=
  ⟨hc, h.noFault, h.live, h.mesh, h.empty, h.inj, h.bound, h.free, h.freeNodup, h.next⟩

/-- Rebuilding a chunk keeps everything in agreement and makes that chunk clean. -/
theorem Synced.remesh {dirty : ChunkPos → Prop} {r : Renderer} {w : World} {g : Gpu}
    (h : Synced dirty r w g) (c : ChunkPos) :
    Synced (fun c' => dirty c' ∧ c' ≠ c) (r.remesh w c).1 w (g.run (r.remesh w c).2) := by
  have hv := loadAround_valid h.cache (w := w) c
  exact (h.withCache hv).setMesh c (meshChunk_cache hv c)

/-- Dropping a chunk keeps everything in agreement. -/
theorem Synced.drop {dirty : ChunkPos → Prop} {r : Renderer} {w : World} {g : Gpu}
    (h : Synced dirty r w g) (c : ChunkPos) :
    Synced dirty (r.drop c).1 w (g.run (r.drop c).2) := by
  have hold : ∀ (c' : ChunkPos) (s' : Nat), (r.slots.erase c)[c']? = some s' →
      c' ≠ c ∧ r.slots[c']? = some s' := by
    intro c' s' hs'
    rw [Std.HashMap.getElem?_erase] at hs'
    split at hs'
    · cases hs'
    · next hcc => exact ⟨fun e => hcc (by simp [e]), hs'⟩
  unfold Renderer.drop
  by_cases hslot : r.slots[c]?.getD 0 ≠ 0
  · have hc := slot_of_getD_ne_zero hslot
    generalize r.slots[c]?.getD 0 = s at hslot hc ⊢
    have hlive := h.live c s hc hslot
    have hif : (s ≠ 0) = True := eq_true hslot
    have hother : ∀ (c' : ChunkPos) (s' : Nat), c' ≠ c → r.slots[c']? = some s' → s' ≠ 0 → s' ≠ s :=
      fun c' s' hcc hs' h0 e => hcc (h.inj c' c s' hs' (e ▸ hc) h0)
    simp only [hif, ↓reduceIte, Gpu.run, List.foldl_cons, List.foldl_nil, Gpu.exec_unload g hlive]
    refine { cache := h.cache, noFault := h.noFault, live := ?_, mesh := ?_, empty := ?_,
             inj := ?_, bound := ?_, free := ?_, freeNodup := ?_, next := h.next }
    · intro c' s' hs' h0
      obtain ⟨hcc, ho⟩ := hold c' s' hs'
      simp only [Std.HashMap.contains_erase, Bool.and_eq_true, Bool.not_eq_true',
        beq_eq_false_iff_ne, ne_eq]
      exact ⟨fun e => hother c' s' hcc ho h0 e.symm, h.live c' s' ho h0⟩
    · intro c' s' hs' h0 hd
      obtain ⟨hcc, ho⟩ := hold c' s' hs'
      rw [Std.HashMap.getElem?_erase]
      have : (s == s') = false := by simpa using fun e => hother c' s' hcc ho h0 e.symm
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      exact h.mesh c' s' ho h0 hd
    · exact fun c' hs' hd => h.empty c' (hold c' 0 hs').2 hd
    · exact fun c1 c2 s' h1 h2 h0 => h.inj c1 c2 s' (hold c1 s' h1).2 (hold c2 s' h2).2 h0
    · exact fun c' s' hs' => h.bound c' s' (hold c' s' hs').2
    · intro s' hs'
      rcases List.mem_cons.mp hs' with rfl | hmem
      · refine ⟨Nat.pos_of_ne_zero hslot, h.bound c _ hc, fun c' hnew => ?_⟩
        obtain ⟨hcc, ho⟩ := hold c' _ hnew
        exact hcc (h.inj c' c _ ho hc hslot)
      · obtain ⟨h1, h2, h3⟩ := h.free s' hmem
        exact ⟨h1, h2, fun c' hnew => h3 c' (hold c' s' hnew).2⟩
    · rw [List.nodup_cons]
      exact ⟨fun hmem => (h.free s hmem).2.2 c hc, h.freeNodup⟩
  · have hslot0 : r.slots[c]?.getD 0 = 0 := by simpa using hslot
    simp only [hslot0, ne_eq, not_true_eq_false, ↓reduceIte, Gpu.run, List.foldl_nil]
    refine { cache := h.cache, noFault := h.noFault, live := ?_, mesh := ?_, empty := ?_,
             inj := ?_, bound := ?_, free := ?_, freeNodup := h.freeNodup, next := h.next }
    · exact fun c' s' hs' h0 => h.live c' s' (hold c' s' hs').2 h0
    · exact fun c' s' hs' h0 hd => h.mesh c' s' (hold c' s' hs').2 h0 hd
    · exact fun c' hs' hd => h.empty c' (hold c' 0 hs').2 hd
    · exact fun c1 c2 s' h1 h2 h0 => h.inj c1 c2 s' (hold c1 s' h1).2 (hold c2 s' h2).2 h0
    · exact fun c' s' hs' => h.bound c' s' (hold c' s' hs').2
    · intro s' hs'
      obtain ⟨h1, h2, h3⟩ := h.free s' hs'
      exact ⟨h1, h2, fun c' hnew => h3 c' (hold c' s' hnew).2⟩

theorem foldl_forEach (step : Renderer → ChunkPos → Renderer × List GpuCmd) (cs : List ChunkPos)
    (r : Renderer) (acc : List GpuCmd) :
    cs.foldl (fun acc c => ((step acc.1 c).1, acc.2 ++ (step acc.1 c).2)) (r, acc)
      = ((forEach step r cs).1, acc ++ (forEach step r cs).2) := by
  induction cs generalizing r acc with
  | nil => simp [forEach]
  | cons c cs ih =>
    simp only [forEach, List.foldl_cons]
    rw [ih, ih (acc := [] ++ _)]
    simp [List.append_assoc]

theorem forEach_cons (step : Renderer → ChunkPos → Renderer × List GpuCmd) (r : Renderer)
    (c : ChunkPos) (cs : List ChunkPos) :
    forEach step r (c :: cs)
      = ((forEach step (step r c).1 cs).1, (step r c).2 ++ (forEach step (step r c).1 cs).2) := by
  simp only [forEach, List.foldl_cons, List.nil_append]
  exact foldl_forEach step cs _ _

/-- Rebuilding a list of chunks makes all of them clean. -/
theorem Synced.forEach_remesh {dirty : ChunkPos → Prop} {r : Renderer} {w : World} {g : Gpu}
    (h : Synced dirty r w g) (cs : List ChunkPos) :
    Synced (fun c' => dirty c' ∧ c' ∉ cs) (forEach (·.remesh w) r cs).1 w
      (g.run (forEach (·.remesh w) r cs).2) := by
  induction cs generalizing dirty r g with
  | nil => exact h.mono (fun _ hd => ⟨hd, List.not_mem_nil⟩)
  | cons c cs ih =>
    rw [forEach_cons, Gpu.run_append]
    refine (ih (h.remesh c)).mono ?_
    rintro c' ⟨⟨hd, hne⟩, hn⟩
    exact ⟨hd, by simp [hne, hn]⟩

theorem Synced.forEach_drop {dirty : ChunkPos → Prop} {r : Renderer} {w : World} {g : Gpu}
    (h : Synced dirty r w g) (cs : List ChunkPos) :
    Synced dirty (forEach Renderer.drop r cs).1 w (g.run (forEach Renderer.drop r cs).2) := by
  induction cs generalizing r g with
  | nil => exact h
  | cons c cs ih =>
    rw [forEach_cons, Gpu.run_append]
    exact ih (h.drop c)

theorem alloc_slots {r r' : Renderer} {s : Nat} (ha : r.alloc = some (s, r')) :
    r'.slots = r.slots := by
  unfold alloc at ha
  split at ha
  · cases ha; rfl
  · split at ha
    · cases ha; rfl
    · cases ha

/-- Recording one chunk's mesh does not touch any other chunk's slot. -/
theorem slots_setMesh_of_ne (r : Renderer) {c c' : ChunkPos} (v : ByteArray) (h : c' ≠ c) :
    (r.setMesh c v).1.slots[c']? = r.slots[c']? := by
  have hb : (c == c') = false := by simpa using fun e => h e.symm
  unfold Renderer.setMesh
  simp only []
  split
  · split
    · simp [Std.HashMap.getElem?_insert, hb]
    · rfl
  · split
    · simp [Std.HashMap.getElem?_insert, hb]
    · split
      · next ha => simp [Std.HashMap.getElem?_insert, hb, alloc_slots ha]
      · simp [Std.HashMap.getElem?_erase, hb]

theorem slots_forEach_remesh_of_not_mem (w : World) (cs : List ChunkPos) (r : Renderer)
    {c' : ChunkPos} (h : c' ∉ cs) :
    (forEach (·.remesh w) r cs).1.slots[c']? = r.slots[c']? := by
  induction cs generalizing r with
  | nil => rfl
  | cons c cs ih =>
    rw [forEach_cons]
    simp only []
    rw [ih _ (fun hm => h (List.mem_cons_of_mem _ hm))]
    exact slots_setMesh_of_ne _ _ (fun e => h (e ▸ List.mem_cons_self))

/--
**Edits keep the picture right.** After the world changes at one block and the
planner follows, every meshed chunk again holds exactly the world's mesh.
-/
theorem Synced.applyEdit {r : Renderer} {w : World} {g : Gpu} (h : Synced (fun _ => False) r w g)
    (p : BlockPos) (b : Block) :
    Synced (fun _ => False) (r.applyEdit (w.set p b) p b).1 (w.set p b)
      (g.run (r.applyEdit (w.set p b) p b).2) := by
  have h1 : Synced (· ∈ dirtyChunks p) { r with cache := r.cache.setBlock p b } (w.set p b) g :=
    { cache := h.cache.setBlock p b
      noFault := h.noFault
      live := h.live
      mesh := fun c s hs h0 hd => by
        rw [meshChunk_set_of_not_dirty w p b hd]
        exact h.mesh c s hs h0 (fun x => x)
      empty := fun c hs hd => by
        rw [meshChunk_set_of_not_dirty w p b hd]
        exact h.empty c hs (fun x => x)
      inj := h.inj
      bound := h.bound
      free := h.free
      freeNodup := h.freeNodup
      next := h.next }
  refine (h1.forEach_remesh _).clear ?_
  rintro c ⟨hd, hn⟩
  rw [slots_forEach_remesh_of_not_mem _ _ _ hn]
  have hc : r.slots.contains c = false := by
    cases hcon : r.slots.contains c
    · rfl
    · exact absurd (List.mem_filter.mpr ⟨hd, hcon⟩) hn
  exact Std.HashMap.getElem?_eq_none_of_contains_eq_false hc

theorem foldl_unload_valid {cache : ChunkCache} {w : World} (h : cache.Valid w)
    (cs : List ChunkPos) : (cs.foldl ChunkCache.unload cache).Valid w := by
  induction cs generalizing cache with
  | nil => exact h
  | cons c cs ih => exact ih (h.unload c)

theorem Synced.dropFar {dirty : ChunkPos → Prop} {r : Renderer} {w : World} {g : Gpu}
    (h : Synced dirty r w g) (view : ViewRange) (centre : ChunkPos) :
    Synced dirty (r.dropFar view centre).1 w (g.run (r.dropFar view centre).2) := by
  have h1 := h.forEach_drop ((r.slots.toList.map (·.1)).filter (view.isFar centre · 1))
  exact h1.withCache (foldl_unload_valid h1.cache _)

/-! ## Starting over -/

theorem slots_drop (r : Renderer) (c : ChunkPos) : (r.drop c).1.slots = r.slots.erase c := by
  unfold Renderer.drop
  simp only []
  split <;> rfl

theorem slots_forEach_drop (cs : List ChunkPos) (r : Renderer) (c' : ChunkPos) :
    (forEach Renderer.drop r cs).1.slots[c']? = if c' ∈ cs then none else r.slots[c']? := by
  induction cs generalizing r with
  | nil => simp [forEach]
  | cons c cs ih =>
    rw [forEach_cons]
    simp only []
    rw [ih, slots_drop, Std.HashMap.getElem?_erase]
    by_cases h1 : c' ∈ cs
    · simp [h1]
    · by_cases h2 : c = c'
      · simp [h2]
      · have : c' ≠ c := fun e => h2 e.symm
        simp [h1, h2, this]

/--
**Loading another world leaves nothing behind.** After a reset no chunk holds a
slot, so the planner and the graphics side agree with any world at all.
-/
theorem Synced.reset {dirty : ChunkPos → Prop} {r : Renderer} {w : World} {g : Gpu}
    (h : Synced dirty r w g) (w' : World) :
    Synced (fun _ => False) r.reset.1 w' (g.run r.reset.2) := by
  have h1 := h.forEach_drop (r.slots.toList.map (·.1))
  have hnone : ∀ c : ChunkPos,
      (forEach Renderer.drop r (r.slots.toList.map (·.1))).1.slots[c]? = none := by
    intro c
    rw [slots_forEach_drop]
    split
    · rfl
    · next hn =>
      cases hc : r.slots[c]? with
      | none => rfl
      | some s =>
        exact absurd (List.mem_map.mpr
          ⟨(c, s), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hc, rfl⟩) hn
  have hslots : ∀ (c : ChunkPos) (s : Nat), r.reset.1.slots[c]? ≠ some s := fun c s hs => by
    have : r.reset.1.slots[c]? = none := hnone c
    rw [this] at hs
    cases hs
  exact {
    cache := ChunkCache.valid_empty w'
    noFault := h1.noFault
    live := fun c s hs => absurd hs (hslots c s)
    mesh := fun c s hs => absurd hs (hslots c s)
    empty := fun c hs => absurd hs (hslots c 0)
    inj := fun c c' s hs => absurd hs (hslots c s)
    bound := fun c s hs => absurd hs (hslots c s)
    free := h1.free
    freeNodup := h1.freeNodup
    next := h1.next }

/-! ## The scene -/

theorem run_draws (g : Gpu) (eye : Vec3) (l : List (ChunkPos × Nat))
    (hl : ∀ c s, (c, s) ∈ l → s ≠ 0 → g.meshes.contains s = true) :
    g.run (l.filterMap fun (c, s) => if s = 0 then none else some (.draw s (chunkOffset c eye)))
      = { g with scene := g.scene ++ l.filterMap fun (c, s) =>
            if s = 0 then none else some (s, chunkOffset c eye) } := by
  induction l generalizing g with
  | nil => simp [Gpu.run]
  | cons x xs ih =>
    obtain ⟨c, s⟩ := x
    by_cases hs : s = 0
    · simp only [List.filterMap_cons, hs, ↓reduceIte]
      exact ih g (fun c' s' hm => hl c' s' (List.mem_cons_of_mem _ hm))
    · have hlive := hl c s List.mem_cons_self hs
      simp only [List.filterMap_cons, hs, ↓reduceIte, Gpu.run, List.foldl_cons, Gpu.exec, hlive]
      have := ih { g with scene := g.scene ++ [(s, chunkOffset c eye)] }
        (fun c' s' hm => hl c' s' (List.mem_cons_of_mem _ hm))
      simp only [Gpu.run] at this
      rw [this]
      simp [List.append_assoc]

/--
**The scene is exactly the meshed chunks.** Drawing a frame faults nothing,
leaves the mesh table alone, and puts in the scene one draw for each chunk that
has something to draw, at that chunk's position relative to the eye.
-/
theorem Synced.draw {r : Renderer} {w : World} {g : Gpu} (h : Synced (fun _ => False) r w g)
    (eye : Vec3) :
    Synced (fun _ => False) r w (g.run (r.drawCmds eye)) ∧
      (g.run (r.drawCmds eye)).meshes = g.meshes ∧
      (g.run (r.drawCmds eye)).scene = r.slots.toList.filterMap fun (c, s) =>
        if s = 0 then none else some (s, chunkOffset c eye) := by
  have hrun := run_draws { g with scene := [] } eye r.slots.toList (fun c s hm h0 =>
    h.live c s (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hm) h0)
  have hcmds : g.run (r.drawCmds eye)
      = { g with scene := r.slots.toList.filterMap fun (c, s) =>
            if s = 0 then none else some (s, chunkOffset c eye) } := by
    simp only [drawCmds, Gpu.run, List.foldl_cons, Gpu.exec]
    simp only [Gpu.run] at hrun
    rw [hrun]
    simp
  rw [hcmds]
  exact ⟨⟨h.cache, h.noFault, h.live, h.mesh, h.empty, h.inj, h.bound, h.free, h.freeNodup,
    h.next⟩, rfl, rfl⟩

/--
**What is drawn is what is there.** Every draw in a frame's scene is some
loaded chunk's slot, placed at that chunk's position, and the slot holds
exactly the world's mesh for that chunk.
-/
theorem Synced.scene_sound {r : Renderer} {w : World} {g : Gpu}
    (h : Synced (fun _ => False) r w g) (eye : Vec3) {s : Nat} {offset : Vec3}
    (hm : (s, offset) ∈ (g.run (r.drawCmds eye)).scene) :
    ∃ c, r.slots[c]? = some s ∧ offset = chunkOffset c eye
      ∧ (g.run (r.drawCmds eye)).meshes[s]? = some (meshChunk w.get c) := by
  obtain ⟨-, hmesh, hscene⟩ := h.draw eye
  rw [hscene, List.mem_filterMap] at hm
  obtain ⟨⟨c, s'⟩, hmem, hval⟩ := hm
  have hslot := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem
  simp only at hval
  split at hval
  · cases hval
  · next h0 =>
    cases hval
    exact ⟨c, hslot, rfl, hmesh ▸ h.mesh c s hslot h0 (fun x => x)⟩

/--
**Nothing loaded is left out.** Every meshed chunk with something to draw is
drawn; a meshed chunk that is not drawn has an empty mesh.
-/
theorem Synced.scene_complete {r : Renderer} {w : World} {g : Gpu}
    (h : Synced (fun _ => False) r w g) (eye : Vec3) {c : ChunkPos} {s : Nat}
    (hs : r.slots[c]? = some s) :
    (s ≠ 0 → (s, chunkOffset c eye) ∈ (g.run (r.drawCmds eye)).scene)
      ∧ (s = 0 → (meshChunk w.get c).size = 0) := by
  refine ⟨fun h0 => ?_, fun h0 => h.empty c (h0 ▸ hs) (fun x => x)⟩
  rw [(h.draw eye).2.2, List.mem_filterMap]
  exact ⟨(c, s), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hs, by simp [h0]⟩

end Renderer

end LeanMc
