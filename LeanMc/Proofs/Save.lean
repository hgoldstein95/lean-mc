import LeanMc.Core.Save
import LeanMc.Proofs.Generated

/-!
# Save theorems

* **Encoding loses nothing.** Decoding the integers a saved game encodes to
  gives back exactly that saved game.
* **Save and load is the identity.** For any sound session of a generated
  world, loading its snapshot succeeds and gives a session with the same
  player, the same inventory, the same selected slot, and the same block at
  every position in the world.

Turning the integers into text and back, and reading and writing the file, are
not proved; they are tested.
-/

namespace LeanMc

theorem Block.ofNat?_toNat (b : Block) : Block.ofNat? b.toNat = some b := by
  cases b <;> rfl

namespace SaveData

theorem decodeBool?_encodeBool (b : Bool) : decodeBool? (encodeBool b) = some b := by
  cases b <;> rfl

theorem decodeSlot?_some (s : Stack) :
    decodeSlot? (s.block.toNat : Int) (s.count : Int) = some (some s) := by
  have hlt := s.extra.isLt
  have hc : ((s.count : Nat) : Int) ≠ 0 := by simp [Stack.count]; omega
  have hr : 1 ≤ ((s.count : Nat) : Int) ∧ ((s.count : Nat) : Int) ≤ 64 := by
    simp only [Stack.count]; omega
  simp only [decodeSlot?, hc, ↓reduceIte, hr, and_self, ↓reduceDIte, Int.toNat_natCast,
    Block.ofNat?_toNat, Option.bind_some, Int.natCast_nonneg]
  congr 2
  cases s with
  | mk block extra =>
    simp only [Stack.count, Stack.mk.injEq, true_and]
    ext
    simp

theorem decodeSlots?_encode (slots : List (Option Stack)) (rest : List Int) :
    decodeSlots? slots.length (slots.flatMap encodeSlot ++ rest) = some (slots, rest) := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
    cases slot with
    | none =>
      simp only [List.length_cons, List.flatMap_cons, encodeSlot, List.cons_append,
        List.nil_append, decodeSlots?, ih]
      rfl
    | some s =>
      simp only [List.length_cons, List.flatMap_cons, encodeSlot, List.cons_append,
        List.nil_append, decodeSlots?, decodeSlot?_some, ih]
      rfl

theorem decodeEdits?_encode (edits : List (BlockPos × Block)) :
    decodeEdits? edits.length (edits.flatMap encodeEdit) = some edits := by
  induction edits with
  | nil => rfl
  | cons e es ih =>
    simp only [List.length_cons, List.flatMap_cons, encodeEdit, List.cons_append, List.nil_append,
      decodeEdits?, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast, Block.ofNat?_toNat,
      Option.bind_some, ih, Option.map_some]

/-- **Encoding loses nothing.** -/
theorem decode?_encode (d : SaveData) : decode? d.encode = some d := by
  have hseed : ((d.seed.toNat : Nat) : Int) < 18446744073709551616 := by
    have := d.seed.toNat_lt
    omega
  have hsel : (0 : Int) ≤ (d.selected.val : Nat) ∧ ((d.selected.val : Nat) : Int) < 9 := by
    have := d.selected.isLt
    omega
  have hslots := decodeSlots?_encode d.inventory.slots.toList
    ((d.edits.length : Int) :: d.edits.flatMap encodeEdit)
  rw [Vector.length_toList] at hslots
  simp only [encode, List.cons_append, List.nil_append, decode?, Int.natCast_nonneg,
    hseed, and_self, ↓reduceIte, hsel, ↓reduceDIte, decodeBool?_encodeBool, Option.bind_some,
    hslots, Vector.length_toList, Int.toNat_natCast, decodeEdits?_encode, Option.map_some]
  congr 1
  cases d with
  | mk seed player inventory selected edits =>
    cases player
    cases inventory
    simp [Vector.toList]

end SaveData

/-! ## Rebuilding a world from its list of edits -/

namespace World

theorem setMany_cons (w : World) (e : BlockPos × Block) (es : List (BlockPos × Block)) :
    w.setMany (e :: es) = (w.set e.1 e.2).setMany es := rfl

/-- Replaying edits to distinct cells: each cell holds its edit, the rest are untouched. -/
theorem get_setMany_distinct (w : World) (es : List (BlockPos × Block))
    (hd : es.Pairwise fun a b => a.1 ≠ b.1) (p : BlockPos) :
    (w.setMany es).get p =
      match es.find? (fun e => e.1 == p) with
      | some e => e.2
      | none => w.get p := by
  induction es generalizing w with
  | nil => rfl
  | cons e es ih =>
    rw [List.pairwise_cons] at hd
    rw [setMany_cons]
    by_cases he : e.1 = p
    · have hfind : (e :: es).find? (fun e => e.1 == p) = some e := by simp [he]
      rw [hfind, get_setMany_of_not_mem _ _ _ (fun a ha => he ▸ (hd.1 a ha).symm), he]
      exact get_set_self ..
    · have hfind : (e :: es).find? (fun e => e.1 == p) = es.find? (fun e => e.1 == p) := by
        simp [he]
      rw [hfind, ih _ hd.2]
      split
      · rfl
      · exact get_set_of_ne _ _ (fun e' => he e'.symm)

/-- Replaying a world's own edits over its terrain gives the same block everywhere. -/
theorem get_setMany_toList (w : World) (m : Std.HashMap BlockPos Block) (p : BlockPos) :
    (w.setMany m.toList).get p = (m[p]?).getD (w.get p) := by
  have hd : m.toList.Pairwise fun a b => a.1 ≠ b.1 :=
    Std.HashMap.distinct_keys_toList.imp (fun h e => by simp [e] at h)
  rw [get_setMany_distinct _ _ hd]
  cases hf : m.toList.find? (fun e => e.1 == p) with
  | none =>
    cases hm : m[p]? with
    | none => rfl
    | some v =>
      have hmem := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hm
      have := List.find?_eq_none.mp hf (p, v) hmem
      simp at this
  | some e =>
    have hmem := List.mem_of_find?_eq_some hf
    have hkey : e.1 = p := by simpa using List.find?_some hf
    have := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem
    rw [hkey] at this
    simp [this]

end World

namespace SaveData

/--
**Save and load is the identity.** For any sound session whose world was
generated from `seed`, loading its snapshot succeeds, and the session it gives
has the same player, the same inventory, the same selected slot, and the same
block at every position.
-/
theorem restore?_snapshot (s : Session) (seed : UInt64)
    (hterrain : s.state.world.terrain = Terrain.generate seed) :
    ∃ s', (s.snapshot seed).restore? = some s' ∧ s'.state.player = s.state.player
      ∧ s'.state.inventory = s.state.inventory ∧ s'.state.selected = s.state.selected
      ∧ ∀ p, s'.state.world.get p = s.state.world.get p := by
  have hget : ∀ p, ((Terrain.world seed).setMany s.state.world.edits.toList).get p
      = s.state.world.get p := by
    intro p
    rw [World.get_setMany_toList, Terrain.world_get]
    simp only [World.get, hterrain]
    cases s.state.world.edits[p]? <;> rfl
  have hfloor : (s.snapshot seed).edits.all (fun e => e.1.y != 0 || e.2 == .bedrock) = true := by
    rw [List.all_eq_true]
    intro e he
    have hm := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp (show (e.1, e.2) ∈ _ from he)
    by_cases hy : e.1.y = 0
    · have hfl := s.sound.floor e.1.x e.1.z
      have hpos : (⟨e.1.x, 0, e.1.z⟩ : BlockPos) = e.1 := by ext <;> simp [hy]
      rw [hpos] at hfl
      simp only [World.get, hm] at hfl
      simp [hfl]
    · simp [hy]
  have hsolid : ((Terrain.world seed).setMany s.state.world.edits.toList).solid
      = s.state.world.solid := funext fun p => by simp only [World.solid, hget]
  have hstart : Player.blocked ((Terrain.world seed).setMany s.state.world.edits.toList).solid
        s.state.player.pos = false ∧ 65536 ≤ s.state.player.pos.y
      ∧ ∀ i : Fin 9, (s.state.inventory.slots[i].map (·.block)) ≠ some .air := by
    refine ⟨?_, s.sound.above, fun i => ?_⟩
    · rw [hsolid]
      exact Player.blocked_eq_false_iff.mpr s.sound.free
    · cases hs : s.state.inventory.slots[i] with
      | none => simp
      | some st =>
        have := s.sound.items i st hs
        simpa using this
  have hres : ∃ s', (s.snapshot seed).restore? = some s' ∧ s'.state =
      { world := (Terrain.world seed).setMany s.state.world.edits.toList
        player := s.state.player, inventory := s.state.inventory
        selected := s.state.selected } := by
    unfold restore?
    split
    · unfold Session.start?
      split
      · exact ⟨_, rfl, rfl⟩
      · next hn => exact absurd hstart hn
    · next hn => exact absurd hfloor hn
  obtain ⟨s', hs', hstate⟩ := hres
  exact ⟨s', hs', by rw [hstate], by rw [hstate], by rw [hstate], fun p => by rw [hstate]; exact hget p⟩

/-- The same, through the integer encoding: what is written is what is read back. -/
theorem restore?_decode_encode (s : Session) (seed : UInt64)
    (hterrain : s.state.world.terrain = Terrain.generate seed) :
    ∃ s', (decode? (s.snapshot seed).encode).bind restore? = some s'
      ∧ s'.state.player = s.state.player ∧ s'.state.inventory = s.state.inventory
      ∧ s'.state.selected = s.state.selected
      ∧ ∀ p, s'.state.world.get p = s.state.world.get p := by
  rw [decode?_encode, Option.bind_some]
  exact restore?_snapshot s seed hterrain

end SaveData

end LeanMc
