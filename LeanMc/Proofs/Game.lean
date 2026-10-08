import LeanMc.Core.Game
import LeanMc.Proofs.Ray
import LeanMc.Proofs.Player
import LeanMc.Proofs.Inventory

/-!
# Game theorems

* **One edit per tick, within reach.** A tick changes at most one block, and
  that block is within six blocks of the player's eyes along every axis.
* **Nothing is overwritten.** A solid block is only ever left alone or removed;
  placing never replaces one.
* **Bedrock is permanent.**
* **Blocks are conserved.** Digging moves a block from the world to the
  inventory and placing moves one back. For every kind of block, the number
  carried plus the number in any region containing the edited cell is the same
  after a tick as before. Nothing is duplicated and nothing vanishes.
* **The player is never buried.** Neither digging nor placing nor moving puts
  the player inside a solid block.
* **Soundness is an invariant.** Together: starting from a sound state, every
  state reachable by any sequence of commands is sound.
-/

namespace LeanMc

theorem Block.eq_air_of_not_solid {b : Block} (h : b.isSolid = false) : b = .air := by
  cases b <;> first | rfl | cases h

theorem Block.ne_air_of_solid {b : Block} (h : b.isSolid = true) : b ≠ .air := by
  rintro rfl
  cases h

namespace State

/-! ## What a change can be -/

/--
Every change is one of two kinds. Digging: a solid block that is not bedrock
becomes air and goes into the inventory. Placing: an empty cell the player is
not standing in is filled with a block taken from the slot in use.
-/
theorem change_cases {s : State} {cmd : Command} {c : Change} (h : s.change cmd = some c) :
    (c.block = .air ∧ s.world.solid c.pos = true ∧ s.world.get c.pos ≠ .bedrock
        ∧ s.inventory.add (s.world.get c.pos) = some c.inventory)
      ∨ (s.world.solid c.pos = false ∧ ¬ (Player.box s.player.pos).Overlaps c.pos
        ∧ s.inventory.take (s.slot cmd) = some (c.block, c.inventory)) := by
  unfold change at h
  split at h
  · cases h
  · next hit ht =>
    split at h
    · split at h
      · cases h
      · next hb =>
        split at h
        · next inv hadd =>
          cases h
          exact .inl ⟨rfl, Ray.cast_solid ht, hb, hadd⟩
        · cases h
    · split at h
      · split at h
        · next f b inv hf htake =>
          split at h
          · cases h
          · next ho =>
            cases h
            exact .inr ⟨Ray.cast_face_clear ht hf, ho, htake⟩
        · cases h
      · cases h

theorem change_of_edit {s : State} {cmd : Command} {p : BlockPos} {b : Block}
    (h : s.edit cmd = some (p, b)) : ∃ c, s.change cmd = some c ∧ c.pos = p ∧ c.block = b := by
  unfold edit at h
  cases hc : s.change cmd with
  | none => simp [hc] at h
  | some c =>
    simp only [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨c, rfl, h.1, h.2⟩

theorem edit_of_change {s : State} {cmd : Command} {c : Change} (h : s.change cmd = some c) :
    s.edit cmd = some (c.pos, c.block) := by
  simp [edit, h]

theorem edit_eq_none {s : State} {cmd : Command} (h : s.edit cmd = none) :
    s.change cmd = none := by
  cases hc : s.change cmd with
  | none => rfl
  | some c => simp [edit, hc] at h

/--
Every edit is one of two kinds: removing a solid block that is not bedrock, or
filling an empty cell the player is not standing in.
-/
theorem edit_cases {s : State} {cmd : Command} {p : BlockPos} {b : Block}
    (h : s.edit cmd = some (p, b)) :
    (b = .air ∧ s.world.solid p = true ∧ s.world.get p ≠ .bedrock) ∨
      (s.world.solid p = false ∧ ¬ (Player.box s.player.pos).Overlaps p) := by
  obtain ⟨c, hc, rfl, rfl⟩ := change_of_edit h
  rcases change_cases hc with ⟨h1, h2, h3, -⟩ | ⟨h1, h2, -⟩
  · exact .inl ⟨h1, h2, h3⟩
  · exact .inr ⟨h1, h2⟩

/-- The cell a change touches is within six blocks of the eyes along every axis. -/
theorem change_near {s : State} {cmd : Command} {c : Change} (h : s.change cmd = some c) :
    (c.pos.x - s.eye.blockPos.x).natAbs ≤ 6 ∧ (c.pos.y - s.eye.blockPos.y).natAbs ≤ 6
      ∧ (c.pos.z - s.eye.blockPos.z).natAbs ≤ 6 := by
  have hx := Player.clamp_bounds (lo := -reach) (hi := reach) (by decide) cmd.look.x
  have hy := Player.clamp_bounds (lo := -reach) (hi := reach) (by decide) cmd.look.y
  have hz := Player.clamp_bounds (lo := -reach) (hi := reach) (by decide) cmd.look.z
  unfold change at h
  split at h
  · cases h
  · next hit ht =>
    have hw := Ray.cast_within ht
    simp only [Ray.Within, reachVector, reach, Vec3.blockPos] at hw hx hy hz ⊢
    split at h
    · split at h
      · cases h
      · split at h
        · cases h
          dsimp only
          omega
        · cases h
    · split at h
      · split at h
        · next f b inv hf htake =>
          split at h
          · cases h
          · cases h
            dsimp only
            cases f <;> simp only [BlockPos.step] <;> omega
        · cases h
      · cases h

theorem edit_near {s : State} {cmd : Command} {p : BlockPos} {b : Block}
    (h : s.edit cmd = some (p, b)) :
    (p.x - s.eye.blockPos.x).natAbs ≤ 6 ∧ (p.y - s.eye.blockPos.y).natAbs ≤ 6
      ∧ (p.z - s.eye.blockPos.z).natAbs ≤ 6 := by
  obtain ⟨c, hc, rfl, -⟩ := change_of_edit h
  exact change_near hc

/-! ## Progress: edits that should happen do happen -/

/--
**Digging works.** Digging at a targeted block that is not bedrock, with room
to carry it, always removes it.
-/
theorem edit_dig {s : State} {cmd : Command} {hit : RayHit} {inv : Inventory}
    (ht : s.target cmd.look = some hit) (hd : cmd.dig = true)
    (hb : s.world.get hit.block ≠ .bedrock)
    (hroom : s.inventory.add (s.world.get hit.block) = some inv) :
    s.edit cmd = some (hit.block, .air) := by
  simp [edit, change, ht, hd, hb, hroom]

/--
**Placing works.** Placing against a targeted face, with a block in the slot in
use, always fills the cell in front of it unless the player is standing there.
-/
theorem edit_place {s : State} {cmd : Command} {hit : RayHit} {f : Dir} {b : Block}
    {inv : Inventory} (ht : s.target cmd.look = some hit) (hd : cmd.dig = false)
    (hp : cmd.place = true) (hf : hit.face = some f)
    (hhave : s.inventory.take (s.slot cmd) = some (b, inv))
    (ho : ¬ (Player.box s.player.pos).Overlaps (hit.block.step f)) :
    s.edit cmd = some (hit.block.step f, b) := by
  simp [edit, change, ht, hd, hp, hf, hhave, ho]

/-! ## What a tick does to the world -/

theorem step_world (s : State) (cmd : Command) :
    (s.step cmd).world =
      match s.edit cmd with
      | some (p, b) => s.world.set p b
      | none => s.world := by
  cases hc : s.change cmd <;> simp [step, edit, hc]

theorem step_inventory (s : State) (cmd : Command) :
    (s.step cmd).inventory =
      match s.change cmd with
      | some c => c.inventory
      | none => s.inventory := rfl

theorem step_selected (s : State) (cmd : Command) :
    (s.step cmd).selected = cmd.select.getD s.selected := rfl

theorem step_get_of_edit_none {s : State} {cmd : Command} (h : s.edit cmd = none) (q : BlockPos) :
    (s.step cmd).world.get q = s.world.get q := by
  rw [step_world, h]

theorem step_get_of_ne {s : State} {cmd : Command} {p q : BlockPos} {b : Block}
    (h : s.edit cmd = some (p, b)) (hq : q ≠ p) : (s.step cmd).world.get q = s.world.get q := by
  rw [step_world, h]
  exact World.get_set_of_ne _ _ hq

/-- After a tick, the edited cell holds what the edit asked for. -/
theorem step_get_of_edit {s : State} {cmd : Command} {p : BlockPos} {b : Block}
    (h : s.edit cmd = some (p, b)) : (s.step cmd).world.get p = b := by
  rw [step_world, h]
  exact World.get_set_self ..

/-- After digging a targeted block that is not bedrock, with room for it, the block is gone. -/
theorem step_dig {s : State} {cmd : Command} {hit : RayHit} {inv : Inventory}
    (ht : s.target cmd.look = some hit) (hd : cmd.dig = true)
    (hb : s.world.get hit.block ≠ .bedrock)
    (hroom : s.inventory.add (s.world.get hit.block) = some inv) :
    (s.step cmd).world.get hit.block = .air :=
  step_get_of_edit (edit_dig ht hd hb hroom)

/-- After placing a carried block against a face the player is clear of, the block is there. -/
theorem step_place {s : State} {cmd : Command} {hit : RayHit} {f : Dir} {b : Block}
    {inv : Inventory} (ht : s.target cmd.look = some hit) (hd : cmd.dig = false)
    (hp : cmd.place = true) (hf : hit.face = some f)
    (hhave : s.inventory.take (s.slot cmd) = some (b, inv))
    (ho : ¬ (Player.box s.player.pos).Overlaps (hit.block.step f)) :
    (s.step cmd).world.get (hit.block.step f) = b :=
  step_get_of_edit (edit_place ht hd hp hf hhave ho)

/-- **One edit per tick.** There is a single cell outside which a tick changes nothing. -/
theorem step_changes_at_most_one (s : State) (cmd : Command) :
    ∃ p, ∀ q, q ≠ p → (s.step cmd).world.get q = s.world.get q := by
  cases h : s.edit cmd with
  | none => exact ⟨⟨0, 0, 0⟩, fun q _ => step_get_of_edit_none h q⟩
  | some e => exact ⟨e.1, fun q hq => step_get_of_ne (p := e.1) (b := e.2) h hq⟩

/-- **Nothing is overwritten.** A tick leaves each solid block as it was or removes it. -/
theorem step_solid_unchanged_or_air (s : State) (cmd : Command) {q : BlockPos}
    (hq : s.world.solid q = true) :
    (s.step cmd).world.get q = s.world.get q ∨ (s.step cmd).world.get q = .air := by
  cases h : s.edit cmd with
  | none => exact .inl (step_get_of_edit_none h q)
  | some e =>
    obtain ⟨p, b⟩ := e
    by_cases hp : q = p
    · subst hp
      rcases edit_cases h with ⟨rfl, -, -⟩ | ⟨hs, -⟩
      · exact .inr (step_get_of_edit h)
      · rw [hs] at hq
        cases hq
    · exact .inl (step_get_of_ne h hp)

/-- **Bedrock is permanent.** -/
theorem step_bedrock (s : State) (cmd : Command) {q : BlockPos} (hq : s.world.get q = .bedrock) :
    (s.step cmd).world.get q = .bedrock := by
  cases h : s.edit cmd with
  | none => rw [step_get_of_edit_none h, hq]
  | some e =>
    obtain ⟨p, b⟩ := e
    by_cases hp : q = p
    · subst hp
      rcases edit_cases h with ⟨-, -, hb⟩ | ⟨hs, -⟩
      · exact absurd hq hb
      · simp [World.solid, hq, Block.isSolid] at hs
    · rw [step_get_of_ne h hp, hq]

/-! ## Conservation -/

/--
**Blocks are conserved at the edited cell.** For any block other than air, the
number carried plus one if the cell holds that block is the same after the
tick as before.
-/
theorem step_conserves_cell {s : State} {cmd : Command} {c : Change} (h : s.change cmd = some c)
    {b : Block} (hb : b ≠ .air) :
    (s.step cmd).inventory.count b + (if (s.step cmd).world.get c.pos = b then 1 else 0)
      = s.inventory.count b + (if s.world.get c.pos = b then 1 else 0) := by
  have hnew : (s.step cmd).world.get c.pos = c.block := step_get_of_edit (edit_of_change h)
  rw [hnew, step_inventory, h]
  rcases change_cases h with ⟨hair, -, -, hadd⟩ | ⟨hempty, -, htake⟩
  · have hc := Inventory.count_add hadd b
    have : ¬ c.block = b := fun e => hb (e ▸ hair)
    simp only [this, ↓reduceIte, hc, eq_comm (a := b)]
    split <;> rfl
  · have hc := Inventory.count_take htake b
    have hwas : s.world.get c.pos = .air := Block.eq_air_of_not_solid hempty
    have : ¬ Block.air = b := fun e => hb e.symm
    simp only [hwas, this, ↓reduceIte, hc, eq_comm (a := b)]
    split <;> omega

theorem countP_update {α : Type} [DecidableEq α] (f g : α → Bool) (l : List α) (p : α)
    (hn : l.Nodup) (hp : p ∈ l) (h : ∀ q ∈ l, q ≠ p → f q = g q) :
    l.countP f + (g p).toNat = l.countP g + (f p).toNat := by
  induction l with
  | nil => cases hp
  | cons x xs ih =>
    rw [List.nodup_cons] at hn
    by_cases hx : x = p
    · subst hx
      have hsame : xs.countP f = xs.countP g :=
        List.countP_congr fun q hq => by
          rw [h q (List.mem_cons_of_mem _ hq) (fun e => hn.1 (e ▸ hq))]
      rw [List.countP_cons, List.countP_cons, hsame]
      cases f x <;> cases g x <;> simp
    · have hmem : p ∈ xs := (List.mem_cons.mp hp).resolve_left (fun e => hx e.symm)
      have := ih hn.2 hmem (fun q hq hne => h q (List.mem_cons_of_mem _ hq) hne)
      rw [List.countP_cons, List.countP_cons, h x List.mem_cons_self hx]
      omega

/--
**Blocks are conserved.** Take any region of the world that contains the cell
a tick edits, if it edits one. For every kind of block other than air, the
number carried plus the number in the region is the same after the tick as
before: nothing is duplicated and nothing vanishes.
-/
theorem step_conserves (s : State) (cmd : Command) {b : Block} (hb : b ≠ .air)
    (region : List BlockPos) (hn : region.Nodup)
    (hin : ∀ c, s.change cmd = some c → c.pos ∈ region) :
    (s.step cmd).inventory.count b + region.countP (fun q => (s.step cmd).world.get q = b)
      = s.inventory.count b + region.countP (fun q => s.world.get q = b) := by
  cases hc : s.change cmd with
  | none =>
    have hw : ∀ q, (s.step cmd).world.get q = s.world.get q := fun q => by
      rw [step_world]
      simp [edit, hc]
    simp only [step_inventory, hc, hw]
  | some c =>
    have hcell := step_conserves_cell hc hb
    have hcount := countP_update (fun q => decide ((s.step cmd).world.get q = b))
      (fun q => decide (s.world.get q = b)) region c.pos hn (hin c hc)
      (fun q _ hq => by rw [step_get_of_ne (edit_of_change hc) hq])
    simp only [Bool.toNat] at hcount
    split at hcell <;> split at hcell <;> simp_all <;> omega

/-! ## The player and the invariant -/

/-- Neither digging nor placing buries the player. -/
theorem free_after_edit {s : State} (cmd : Command)
    (h : Player.Free s.world.solid s.player.pos) :
    Player.Free (s.step cmd).world.solid s.player.pos := by
  intro q hq
  cases he : s.edit cmd with
  | none =>
    simp only [World.solid, step_get_of_edit_none he]
    exact h q hq
  | some e =>
    obtain ⟨p, b⟩ := e
    by_cases hp : q = p
    · subst hp
      rcases edit_cases he with ⟨rfl, -, -⟩ | ⟨-, ho⟩
      · simp [World.solid, step_get_of_edit he, Block.isSolid]
      · exact absurd hq ho
    · simp only [World.solid, step_get_of_ne he hp]
      exact h q hq

theorem step_player (s : State) (cmd : Command) :
    (s.step cmd).player = s.player.step (s.step cmd).world.solid cmd.move := rfl

/-- **The player is never buried.** A tick, edit and movement together, keeps the player free. -/
theorem step_free {s : State} (cmd : Command) (h : Player.Free s.world.solid s.player.pos) :
    Player.Free (s.step cmd).world.solid (s.step cmd).player.pos := by
  rw [step_player]
  exact Player.step_free cmd.move (free_after_edit cmd h)

/-- Air is never carried: only solid blocks are ever picked up. -/
theorem step_noAir {s : State} (cmd : Command) (h : s.inventory.NoAir) :
    (s.step cmd).inventory.NoAir := by
  rw [step_inventory]
  cases hc : s.change cmd with
  | none => exact h
  | some c =>
    rcases change_cases hc with ⟨-, hsolid, -, hadd⟩ | ⟨-, -, htake⟩
    · exact h.add (Block.ne_air_of_solid hsolid) hadd
    · exact (h.take htake).2

/-- A state in which nothing has gone wrong. -/
structure Sound (s : State) : Prop where
  /-- The player is not inside a solid block. -/
  free : Player.Free s.world.solid s.player.pos
  /-- The bedrock floor is intact. -/
  floor : ∀ x z, s.world.get ⟨x, 0, z⟩ = .bedrock
  /-- The player's feet are above the floor. -/
  above : 65536 ≤ s.player.pos.y
  /-- The player is not carrying air. -/
  items : s.inventory.NoAir

theorem Sound.step {s : State} (h : Sound s) (cmd : Command) : Sound (s.step cmd) where
  free := step_free cmd h.free
  floor x z := step_bedrock s cmd (h.floor x z)
  above := by
    rw [step_player]
    exact Player.step_above_floor
      (fun x z => by
        show ((s.step cmd).world.get ⟨x, 0, z⟩).isSolid = true
        rw [step_bedrock s cmd (h.floor x z)]
        rfl)
      cmd.move h.above
  items := step_noAir cmd h.items

/--
**Soundness is an invariant.** From a sound state, no sequence of commands,
however long or adversarial, buries the player, breaks the floor or drops the
player through it.
-/
theorem Sound.run {s : State} (h : Sound s) (cmds : List Command) : Sound (s.run cmds) := by
  induction cmds generalizing s with
  | nil => exact h
  | cons cmd cmds ih => exact ih (h.step cmd)

end State

end LeanMc
