import LeanMc.Core.Save
import LeanMc.Proofs.Generated

/-!
# Save theorems

* **Encoding loses nothing.** Decoding the integers a saved game encodes to
  gives back exactly that saved game.
* **The format is canonical.** Conversely, whatever decodes to a saved game is
  exactly that game's encoding: no two files mean the same game.
* **Save and load is the identity.** Any session that can be saved, which is
  any session of a generated world, loads again from its snapshot: the result
  cannot be told apart from the original, with the same player, inventory and
  selected slot and the same block at every position, and it remembers the
  same seed.
* **And it stays that way.** The loaded game and the original answer every
  later sequence of commands identically.
* **Every game that can be reached can be saved and loaded.** That holds after
  any frames from a new game's start, with no side condition for the caller.

Turning the integers into text and back, and reading and writing the file, are
not proved; they are tested.
-/

namespace LeanMc

theorem Block.ofNat?_toNat (b : Block) : Block.ofNat? b.toNat = some b := by
  cases b <;> rfl

theorem Block.toNat_of_ofNat? {n : Nat} {b : Block} (h : Block.ofNat? n = some b) :
    b.toNat = n := by
  unfold Block.ofNat? at h
  split at h <;> first | (cases h; rfl) | cases h

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

/-! ### The other direction: decoding determines the integers -/

theorem encodeBool_of_decodeBool? {n : Int} {b : Bool} (h : decodeBool? n = some b) :
    encodeBool b = n := by
  unfold decodeBool? at h
  split at h
  · cases h; simp [encodeBool, *]
  · split at h
    · cases h; simp [encodeBool, *]
    · cases h

theorem encodeSlot_of_decodeSlot? {block count : Int} {slot : Option Stack}
    (h : decodeSlot? block count = some slot) : encodeSlot slot = [block, count] := by
  unfold decodeSlot? at h
  split at h
  · next hc =>
    split at h
    · next hb => cases h; simp [encodeSlot, hb, hc]
    · cases h
  · next hc =>
    split at h
    · next hr =>
      cases hb : Block.ofNat? block.toNat with
      | none => simp [hb] at h
      | some b =>
        simp only [hb, Option.bind_some] at h
        split at h
        · next hnn =>
          cases h
          have := Block.toNat_of_ofNat? hb
          simp only [encodeSlot, Stack.count, this, List.cons.injEq, and_true]
          omega
        · cases h
    · cases h

theorem encode_of_decodeSlots? {n : Nat} {l rest : List Int} {slots : List (Option Stack)}
    (h : decodeSlots? n l = some (slots, rest)) :
    l = slots.flatMap encodeSlot ++ rest ∧ slots.length = n := by
  induction n generalizing l slots with
  | zero =>
    simp only [decodeSlots?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | succ n ih =>
    match l, h with
    | block :: count :: l', h =>
      simp only [decodeSlots?] at h
      cases hs : decodeSlot? block count with
      | none => simp [hs] at h
      | some slot =>
        cases hr : decodeSlots? n l' with
        | none => simp [hs, hr] at h
        | some pair =>
          obtain ⟨slots', rest'⟩ := pair
          simp only [hs, hr, Option.bind_some, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨rfl, hlen⟩ := ih hr
          have := encodeSlot_of_decodeSlot? hs
          simp [this, hlen]
    | [], h => simp [decodeSlots?] at h
    | [_], h => simp [decodeSlots?] at h

theorem encode_of_decodeEdits? {n : Nat} {l : List Int} {edits : List (BlockPos × Block)}
    (h : decodeEdits? n l = some edits) : l = edits.flatMap encodeEdit ∧ edits.length = n := by
  induction n generalizing l edits with
  | zero =>
    cases l with
    | nil => simp only [decodeEdits?, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
    | cons _ _ => simp [decodeEdits?] at h
  | succ n ih =>
    match l, h with
    | x :: y :: z :: block :: l', h =>
      simp only [decodeEdits?] at h
      split at h
      · next hnn =>
        cases hb : Block.ofNat? block.toNat with
        | none => simp [hb] at h
        | some b =>
          cases hr : decodeEdits? n l' with
          | none => simp [hb, hr] at h
          | some es =>
            simp only [hb, hr, Option.bind_some, Option.map_some, Option.some.injEq] at h
            subst h
            obtain ⟨rfl, hlen⟩ := ih hr
            have := Block.toNat_of_ofNat? hb
            simp only [List.flatMap_cons, encodeEdit, this, List.cons_append, List.nil_append,
              List.length_cons, hlen, List.cons.injEq, true_and, and_true]
            omega
      · cases h
    | [], h => simp [decodeEdits?] at h
    | [_], h => simp [decodeEdits?] at h
    | [_, _], h => simp [decodeEdits?] at h
    | [_, _, _], h => simp [decodeEdits?] at h

/--
**The format is canonical.** Whatever integers decode to a saved game are
exactly the integers that game encodes to. So no two files mean the same game,
and a file that has been altered either is refused or means something else.
-/
theorem encode_of_decode? {l : List Int} {d : SaveData} (h : decode? l = some d) :
    d.encode = l := by
  unfold decode? at h
  split at h
  · next m v seed px py pz vx vy vz ground flying selected rest =>
    split at h
    · next hc =>
      split at h
      · next hs =>
        cases hg : decodeBool? ground with
        | none => simp [hg] at h
        | some og =>
          cases hf : decodeBool? flying with
          | none => simp [hg, hf] at h
          | some fl =>
            cases hsl : decodeSlots? 9 rest with
            | none => simp [hg, hf, hsl] at h
            | some pair =>
              obtain ⟨slots, rest'⟩ := pair
              simp only [hg, hf, hsl, Option.bind_some] at h
              split at h
              · next hl =>
                split at h
                · next count rest'' =>
                  split at h
                  · next hcount =>
                    cases he : decodeEdits? count.toNat rest'' with
                    | none => simp [he] at h
                    | some edits =>
                      simp only [he, Option.map_some, Option.some.injEq] at h
                      subst h
                      obtain ⟨rfl, -⟩ := encode_of_decodeSlots? hsl
                      obtain ⟨rfl, hlen⟩ := encode_of_decodeEdits? he
                      have hg' := encodeBool_of_decodeBool? hg
                      have hf' := encodeBool_of_decodeBool? hf
                      obtain ⟨rfl, rfl, hs0, hs1⟩ := hc
                      have hseed : ((seed.toNat.toUInt64.toNat : Nat) : Int) = seed := by
                        have : seed.toNat < 18446744073709551616 := by omega
                        simp [Nat.mod_eq_of_lt this]
                        omega
                      have hcount' : ((edits.length : Nat) : Int) = count := by omega
                      simp only [encode, hg', hf', hseed, List.cons_append, List.nil_append,
                        List.cons.injEq, true_and, hcount']
                      exact ⟨by omega, by simp [Vector.toList]⟩
                  · cases h
                · cases h
              · cases h
      · cases h
    · cases h
  · cases h

/-- A list of integers is a saved game's encoding exactly when it decodes to that game. -/
theorem decode?_eq_some_iff {l : List Int} {d : SaveData} : decode? l = some d ↔ d.encode = l :=
  ⟨encode_of_decode?, fun h => h ▸ decode?_encode d⟩

/-- No two lists of integers decode to the same saved game. -/
theorem decode?_injective {l l' : List Int} {d : SaveData} (h : decode? l = some d)
    (h' : decode? l' = some d) : l = l' :=
  (encode_of_decode? h).symm.trans (encode_of_decode? h')

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

namespace Session

/-- A session can be saved exactly when it knows its seed. -/
theorem snapshot_isSome (s : Session) : s.snapshot.isSome = s.seed.isSome := by
  simp [snapshot]

end Session

namespace SaveData

/--
**Save and load is the identity.** Whatever a session saves, loading it
succeeds and gives a session that cannot be told apart from the original and
remembers the same seed.
-/
theorem restore?_snapshot (s : Session) {d : SaveData} (hd : s.snapshot = some d) :
    ∃ s', d.restore? = some s' ∧ State.Same s'.state s.state ∧ s'.seed = s.seed := by
  cases hseed : s.seed with
  | none => simp [Session.snapshot, hseed] at hd
  | some seed =>
    have hterrain := s.seeded seed hseed
    simp only [Session.snapshot, hseed, Option.map_some, Option.some.injEq] at hd
    subst hd
    have hget : ∀ p, ((Terrain.world seed).setMany s.state.world.edits.toList).get p
        = s.state.world.get p := by
      intro p
      rw [World.get_setMany_toList, Terrain.world_get]
      simp only [World.get, hterrain]
      cases s.state.world.edits[p]? <;> rfl
    have hfloor : s.state.world.edits.toList.all (fun e => e.1.y != 0 || e.2 == .bedrock)
        = true := by
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
    have hcarry : ∀ b : Block, s.state.inventory.Lacks b →
        ∀ i : Fin 9, (s.state.inventory.slots[i].map (·.block)) ≠ some b := by
      intro b hb i
      cases hs : s.state.inventory.slots[i] with
      | none => simp
      | some st =>
        have := hb i st hs
        simpa using this
    have hstart : Player.blocked ((Terrain.world seed).setMany s.state.world.edits.toList).solid
          s.state.player.pos = false ∧ 65536 ≤ s.state.player.pos.y
        ∧ s.state.player.SpeedBounded
        ∧ s.state.player.onGround
          = Player.blocked ((Terrain.world seed).setMany s.state.world.edits.toList).solid
            (s.state.player.pos.add .y (-1))
        ∧ (∀ i : Fin 9, (s.state.inventory.slots[i].map (·.block)) ≠ some .air)
        ∧ (∀ i : Fin 9, (s.state.inventory.slots[i].map (·.block)) ≠ some .bedrock) := by
      refine ⟨?_, s.sound.above, s.sound.speed, ?_, hcarry _ s.sound.items,
        hcarry _ s.sound.bedrock⟩
      · rw [hsolid]
        exact Player.blocked_eq_false_iff.mpr s.sound.free
      · rw [hsolid]
        exact s.sound.grounded
    have hres : ∃ s', restore? (⟨seed, s.state.player, s.state.inventory, s.state.selected,
          s.state.world.edits.toList⟩ : SaveData) = some s'
        ∧ s'.state =
          { world := (Terrain.world seed).setMany s.state.world.edits.toList
            player := s.state.player, inventory := s.state.inventory
            selected := s.state.selected }
        ∧ s'.seed = some seed := by
      unfold restore?
      split
      · unfold Session.start?
        split
        · exact ⟨_, rfl, rfl, rfl⟩
        · next hn => exact absurd hstart hn
      · next hn => exact absurd hfloor hn
    obtain ⟨s', hs', hstate, hsd⟩ := hres
    exact ⟨s', hs', ⟨by rw [hstate], by rw [hstate], by rw [hstate],
      fun p => by rw [hstate]; exact hget p⟩, hsd⟩

/-- The same, through the integer encoding: what is written is what is read back. -/
theorem restore?_decode_encode (s : Session) {d : SaveData} (hd : s.snapshot = some d) :
    ∃ s', (decode? d.encode).bind restore? = some s' ∧ State.Same s'.state s.state
      ∧ s'.seed = s.seed := by
  rw [decode?_encode, Option.bind_some]
  exact restore?_snapshot s hd

/--
**And it stays that way.** A loaded game and the game that was saved answer
every later sequence of commands identically: after any of them the two still
have the same player, inventory, selected slot and blocks.
-/
theorem restore?_snapshot_run (s : Session) {d : SaveData} (hd : s.snapshot = some d)
    (cmds : List Command) :
    ∃ s', (decode? d.encode).bind restore? = some s'
      ∧ State.Same (s'.state.run cmds) (s.state.run cmds) := by
  obtain ⟨s', hs', hsame, -⟩ := restore?_decode_encode s hd
  exact ⟨s', hs', hsame.run cmds⟩

end SaveData

namespace Terrain

/--
**Every game that can be reached can be saved and loaded.** After any frames
from a new game's start, the session has a snapshot, and writing it out and
reading it back gives a session that cannot be told apart from it and that
remembers the same seed, so it can be saved again in turn.
-/
theorem session_save_load (seed : UInt64) (frames : List Frame) :
    ∃ d s', ((session seed).play frames).1.snapshot = some d
      ∧ (SaveData.decode? d.encode).bind SaveData.restore? = some s'
      ∧ State.Same s'.state ((session seed).play frames).1.state ∧ s'.seed = some seed := by
  have hseed : ((session seed).play frames).1.seed = some seed := Session.play_seed _ frames
  cases hd : ((session seed).play frames).1.snapshot with
  | none =>
    have := Session.snapshot_isSome ((session seed).play frames).1
    simp [hd, hseed] at this
  | some d =>
    obtain ⟨s', hs', hsame, hsd⟩ := SaveData.restore?_decode_encode _ hd
    exact ⟨d, s', rfl, hs', hsame, hsd.trans hseed⟩

end Terrain

end LeanMc
