import LeanMc.Core.Game
import LeanMc.Proofs.Ray
import LeanMc.Proofs.RayGeometry
import LeanMc.Proofs.Player
import LeanMc.Proofs.Inventory

/-!
# Game theorems

* **One edit per tick, within reach.** A tick changes at most one block, and
  that block is within five blocks of the player's eyes along every axis.
* **A long look is not bent.** A look vector within reach is used as it is; a
  longer one is scaled down along its own direction.
* **What is targeted is on the line of sight.**
* **Nothing is overwritten.** A solid block is only ever left alone or removed;
  placing never replaces one.
* **Bedrock is permanent, and there is never more of it.** A cell holds bedrock
  after a tick exactly when it did before.
* **There is always a face to place against.** In a sound state the player's
  eyes are never inside a block, so whatever is targeted has a face.
* **Blocks are conserved.** Digging moves a block from the world to the
  inventory and placing moves one back. For every kind of block, the number
  carried plus the number in any region containing the edited cell is the same
  after a tick as before. Nothing is duplicated and nothing vanishes.
* **The player is never buried.** Neither digging nor placing nor moving puts
  the player inside a solid block.
* **Soundness is an invariant.** Together: starting from a sound state, every
  state reachable by any sequence of commands is sound. A sound state also
  keeps the player within the speed limit, aware of whether they stand on
  something, and carrying neither air nor bedrock.
* **Only what can be seen matters.** Two states with the same player, inventory
  and selected slot, and the same block at every position, stay that way under
  any commands, however differently their worlds are stored.
-/

namespace LeanMc

theorem Block.eq_air_of_not_solid {b : Block} (h : b.isSolid = false) : b = .air := by
  cases b <;> first | rfl | cases h

theorem Block.ne_air_of_solid {b : Block} (h : b.isSolid = true) : b ≠ .air := by
  rintro rfl
  cases h

namespace State

/-! ## Reach -/

theorem scaleToReach_bounds {c : Int} {longest : Nat} (h : c.natAbs ≤ longest) :
    -reach ≤ scaleToReach c longest ∧ scaleToReach c longest ≤ reach := by
  have hk : c.natAbs * 327680 / longest ≤ 327680 :=
    Nat.div_le_of_le_mul (Nat.mul_le_mul_right _ h)
  simp only [scaleToReach, reach]
  generalize c.natAbs * 327680 / longest = k at hk
  split <;> omega

/-- Scaling keeps a component's sign and scales its size by `reach / longest`, rounding down. -/
theorem scaleToReach_spec (c : Int) (longest : Nat) :
    (scaleToReach c longest).natAbs = c.natAbs * 327680 / longest
      ∧ (0 ≤ c → 0 ≤ scaleToReach c longest) ∧ (c ≤ 0 → scaleToReach c longest ≤ 0) := by
  by_cases hc : c = 0
  · subst hc
    simp [scaleToReach]
  · simp only [scaleToReach]
    generalize c.natAbs * 327680 / longest = k
    split <;> omega

/-- However long the look vector, what is walked reaches no further than `reach` along any axis. -/
theorem reachVector_bounds (look : Vec3) :
    (-reach ≤ (reachVector look).x ∧ (reachVector look).x ≤ reach)
      ∧ (-reach ≤ (reachVector look).y ∧ (reachVector look).y ≤ reach)
      ∧ (-reach ≤ (reachVector look).z ∧ (reachVector look).z ≤ reach) := by
  simp only [reachVector]
  split
  · simp only [reach]
    omega
  · exact ⟨scaleToReach_bounds (by omega), scaleToReach_bounds (by omega),
      scaleToReach_bounds (by omega)⟩

/-- **A look within reach is used exactly as given.** -/
theorem reachVector_of_within {look : Vec3}
    (h : look.x.natAbs ≤ 327680 ∧ look.y.natAbs ≤ 327680 ∧ look.z.natAbs ≤ 327680) :
    reachVector look = look := by
  have : max look.x.natAbs (max look.y.natAbs look.z.natAbs) ≤ 327680 := by omega
  simp [reachVector, this]

/--
**A long look is not bent.** A look vector too long for the player's reach is
scaled by one factor, `reach / longest`, along every axis, rounding each
component towards zero. So it points where it pointed, and its longest
component is exactly the reach.
-/
theorem reachVector_of_long {look : Vec3}
    (h : 327680 < max look.x.natAbs (max look.y.natAbs look.z.natAbs)) :
    ∀ axis, ((reachVector look).get axis).natAbs
        = (look.get axis).natAbs * 327680 / max look.x.natAbs (max look.y.natAbs look.z.natAbs)
      ∧ (0 ≤ look.get axis → 0 ≤ (reachVector look).get axis)
      ∧ (look.get axis ≤ 0 → (reachVector look).get axis ≤ 0) := by
  have hn : ¬ max look.x.natAbs (max look.y.natAbs look.z.natAbs) ≤ 327680 := by omega
  intro axis
  cases axis <;> simp only [reachVector, hn, ↓reduceIte, Vec3.get] <;>
    exact scaleToReach_spec _ _

/--
**What is targeted is on the line of sight.** The targeted block is touched by
the segment from the player's eyes along the look vector, cut to their reach,
and every cell between is touched by it too and is empty.
-/
theorem target_path {s : State} {look : Vec3} {hit : RayHit} (h : s.target look = some hit) :
    Ray.Path s.world.solid s.eye (reachVector look) s.eye.blockPos hit.block :=
  Ray.cast_path h

theorem target_touches {s : State} {look : Vec3} {hit : RayHit} (h : s.target look = some hit) :
    Ray.Touches s.eye (reachVector look) hit.block :=
  Ray.cast_touches h

/-! ## What a change can be -/

/--
Every change is one of two kinds. Digging: a solid block that is not bedrock
becomes air and goes into the inventory. Placing: an empty cell the player is
not standing in is filled with a block taken from the slot in use. Which it is,
is what the command asked for.
-/
theorem change_cases {s : State} {cmd : Command} {c : Change} (h : s.change cmd = some c) :
    (cmd.action = some .dig ∧ c.block = .air ∧ s.world.solid c.pos = true
        ∧ s.world.get c.pos ≠ .bedrock ∧ s.inventory.add (s.world.get c.pos) = some c.inventory)
      ∨ (cmd.action = some .place ∧ s.world.solid c.pos = false
        ∧ ¬ (Player.box s.player.pos).Overlaps c.pos
        ∧ s.inventory.take (s.slot cmd) = some (c.block, c.inventory)) := by
  unfold change at h
  split at h
  · cases h
  · next hit ht =>
    split at h
    · cases h
    · next ha =>
      split at h
      · cases h
      · next hb =>
        split at h
        · next inv hadd =>
          cases h
          exact .inl ⟨ha, rfl, Ray.cast_solid ht, hb, hadd⟩
        · cases h
    · next ha =>
      split at h
      · next f b inv hf htake =>
        split at h
        · cases h
        · next ho =>
          cases h
          exact .inr ⟨ha, Ray.cast_face_clear ht hf, ho, htake⟩
      · cases h

/-- A command that asks for nothing changes nothing. -/
theorem change_of_no_action {s : State} {cmd : Command} (h : cmd.action = none) :
    s.change cmd = none := by
  unfold change
  split
  · rfl
  · simp [h]

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
  rcases change_cases hc with ⟨-, h1, h2, h3, -⟩ | ⟨-, h1, h2, -⟩
  · exact .inl ⟨h1, h2, h3⟩
  · exact .inr ⟨h1, h2⟩

/--
The cell a change touches is within five blocks of the eyes along every axis:
a dug block because the walk never leaves the box the reach spans, a placed
one because it goes where the walk had just been.
-/
theorem change_near {s : State} {cmd : Command} {c : Change} (h : s.change cmd = some c) :
    (c.pos.x - s.eye.blockPos.x).natAbs ≤ 5 ∧ (c.pos.y - s.eye.blockPos.y).natAbs ≤ 5
      ∧ (c.pos.z - s.eye.blockPos.z).natAbs ≤ 5 := by
  have hb := reachVector_bounds cmd.look
  unfold change at h
  split at h
  · cases h
  · next hit ht =>
    have hw := Ray.cast_within ht
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
          simp only [Ray.Within, reach, Vec3.blockPos] at hw hb ⊢
          omega
        · cases h
    · split at h
      · next f b inv hf htake =>
        have hfw := Ray.cast_face_within ht hf
        split at h
        · cases h
        · cases h
          simp only [Ray.Within, reach, Vec3.blockPos] at hfw hb ⊢
          omega
      · cases h

theorem edit_near {s : State} {cmd : Command} {p : BlockPos} {b : Block}
    (h : s.edit cmd = some (p, b)) :
    (p.x - s.eye.blockPos.x).natAbs ≤ 5 ∧ (p.y - s.eye.blockPos.y).natAbs ≤ 5
      ∧ (p.z - s.eye.blockPos.z).natAbs ≤ 5 := by
  obtain ⟨c, hc, rfl, -⟩ := change_of_edit h
  exact change_near hc

/-! ## Progress: edits that should happen do happen -/

/--
**Digging works.** Digging at a targeted block that is not bedrock, with room
to carry it, always removes it.
-/
theorem edit_dig {s : State} {cmd : Command} {hit : RayHit} {inv : Inventory}
    (ht : s.target cmd.look = some hit) (hd : cmd.action = some .dig)
    (hb : s.world.get hit.block ≠ .bedrock)
    (hroom : s.inventory.add (s.world.get hit.block) = some inv) :
    s.edit cmd = some (hit.block, .air) := by
  simp [edit, change, ht, hd, hb, hroom]

/--
**Placing works.** Placing against a targeted face, with a block in the slot in
use, always fills the cell in front of it unless the player is standing there.
-/
theorem edit_place {s : State} {cmd : Command} {hit : RayHit} {f : Dir} {b : Block}
    {inv : Inventory} (ht : s.target cmd.look = some hit) (hp : cmd.action = some .place)
    (hf : hit.face = some f) (hhave : s.inventory.take (s.slot cmd) = some (b, inv))
    (ho : ¬ (Player.box s.player.pos).Overlaps (hit.block.step f)) :
    s.edit cmd = some (hit.block.step f, b) := by
  simp [edit, change, ht, hp, hf, hhave, ho]

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
    (ht : s.target cmd.look = some hit) (hd : cmd.action = some .dig)
    (hb : s.world.get hit.block ≠ .bedrock)
    (hroom : s.inventory.add (s.world.get hit.block) = some inv) :
    (s.step cmd).world.get hit.block = .air :=
  step_get_of_edit (edit_dig ht hd hb hroom)

/-- After placing a carried block against a face the player is clear of, the block is there. -/
theorem step_place {s : State} {cmd : Command} {hit : RayHit} {f : Dir} {b : Block}
    {inv : Inventory} (ht : s.target cmd.look = some hit) (hp : cmd.action = some .place)
    (hf : hit.face = some f) (hhave : s.inventory.take (s.slot cmd) = some (b, inv))
    (ho : ¬ (Player.box s.player.pos).Overlaps (hit.block.step f)) :
    (s.step cmd).world.get (hit.block.step f) = b :=
  step_get_of_edit (edit_place ht hp hf hhave ho)

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
  rcases change_cases h with ⟨-, hair, -, -, hadd⟩ | ⟨-, hempty, -, htake⟩
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

/--
**Blocks are conserved over any run of commands.** Take any region containing
every cell the run edits. For every kind of block other than air, the number
carried plus the number in the region is the same at the end as at the start.
-/
theorem run_conserves (s : State) (cmds : List Command) {b : Block} (hb : b ≠ .air)
    (region : List BlockPos) (hn : region.Nodup)
    (hin : ∀ (before : List Command) (cmd : Command) (after : List Command) (c : Change),
      cmds = before ++ cmd :: after → (s.run before).change cmd = some c → c.pos ∈ region) :
    (s.run cmds).inventory.count b + region.countP (fun q => (s.run cmds).world.get q = b)
      = s.inventory.count b + region.countP (fun q => s.world.get q = b) := by
  induction cmds generalizing s with
  | nil => rfl
  | cons cmd cmds ih =>
    have h1 := step_conserves s cmd hb region hn (fun c hc => hin [] cmd cmds c rfl hc)
    have h2 := ih (s.step cmd) (fun before cmd' after c he hc =>
      hin (cmd :: before) cmd' after c (by rw [he]; rfl) hc)
    exact h2.trans h1

/-! ## The terrain -/

/-- A tick never changes the terrain under the edits. -/
theorem step_terrain (s : State) (cmd : Command) :
    (s.step cmd).world.terrain = s.world.terrain := by
  simp only [step]
  cases s.change cmd <;> rfl

theorem run_terrain (s : State) (cmds : List Command) :
    (s.run cmds).world.terrain = s.world.terrain := by
  induction cmds generalizing s with
  | nil => rfl
  | cons c cs ih => exact (ih (s.step c)).trans (s.step_terrain c)

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
    rcases change_cases hc with ⟨-, -, hsolid, -, hadd⟩ | ⟨-, -, -, htake⟩
    · exact Inventory.Lacks.add h (Block.ne_air_of_solid hsolid) hadd
    · exact (Inventory.Lacks.take h htake).2

/-- Bedrock is never carried: it cannot be dug, so it is never picked up. -/
theorem step_noBedrock {s : State} (cmd : Command) (h : s.inventory.Lacks .bedrock) :
    (s.step cmd).inventory.Lacks .bedrock := by
  rw [step_inventory]
  cases hc : s.change cmd with
  | none => exact h
  | some c =>
    rcases change_cases hc with ⟨-, -, -, hb, hadd⟩ | ⟨-, -, -, htake⟩
    · exact Inventory.Lacks.add h hb hadd
    · exact (Inventory.Lacks.take h htake).2

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
  /-- The player is not carrying bedrock, which can be neither dug nor, therefore, placed. -/
  bedrock : s.inventory.Lacks .bedrock
  /-- No axis of the player's velocity is beyond the speed limit. -/
  speed : s.player.SpeedBounded
  /-- The player knows whether they are standing on something. -/
  grounded : s.player.onGround = Player.blocked s.world.solid (s.player.pos.add .y (-1))

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
  bedrock := step_noBedrock cmd h.bedrock
  speed := by
    rw [step_player]
    exact Player.step_speedBounded _ _ h.speed
  grounded := rfl

/--
**Soundness is an invariant.** From a sound state, no sequence of commands,
however long or adversarial, buries the player, breaks the floor or drops the
player through it.
-/
theorem Sound.run {s : State} (h : Sound s) (cmds : List Command) : Sound (s.run cmds) := by
  induction cmds generalizing s with
  | nil => exact h
  | cons cmd cmds ih => exact ih (h.step cmd)

/-! ## What soundness buys -/

/--
**There is always a face to place against.** In a sound state the player's
eyes are inside the player's own box, which is clear of blocks, so the walk
never starts inside one and whatever it hits has a face.
-/
theorem Sound.target_face {s : State} (h : s.Sound) {look : Vec3} {hit : RayHit}
    (ht : s.target look = some hit) : ∃ f, hit.face = some f := by
  cases hf : hit.face with
  | some f => exact ⟨f, rfl⟩
  | none =>
    exfalso
    have hsolid := Ray.cast_face_none ht hf
    have hov : (Player.box s.player.pos).Overlaps s.eye.blockPos := by
      simp only [Box.Overlaps, Player.box, State.eye, Vec3.add, Vec3.blockPos, Player.halfWidth,
        Player.height, Player.eyeHeight]
      omega
    have := h.free _ hov
    simp only [World.solid] at this hsolid
    rw [this] at hsolid
    cases hsolid

/--
**Placing works, in a sound state.** Asking to place while targeting a block,
with a block in the slot in use, always fills the cell in front of the targeted
face unless the player is standing there. Nothing else can refuse it.
-/
theorem Sound.edit_place {s : State} (h : s.Sound) {cmd : Command} {hit : RayHit} {b : Block}
    {inv : Inventory} (ht : s.target cmd.look = some hit) (hp : cmd.action = some .place)
    (hhave : s.inventory.take (s.slot cmd) = some (b, inv))
    (ho : ∀ f, hit.face = some f → ¬ (Player.box s.player.pos).Overlaps (hit.block.step f)) :
    ∃ f, hit.face = some f ∧ s.edit cmd = some (hit.block.step f, b) := by
  obtain ⟨f, hf⟩ := h.target_face ht
  exact ⟨f, hf, State.edit_place ht hp hf hhave (ho f hf)⟩

/--
**There is never more bedrock.** In a sound state nobody carries bedrock, so
none can be placed: a cell holds bedrock after a tick exactly when it did
before. Bedrock is not only permanent, it is fixed.
-/
theorem Sound.step_bedrock_iff {s : State} (h : s.Sound) (cmd : Command) (q : BlockPos) :
    (s.step cmd).world.get q = .bedrock ↔ s.world.get q = .bedrock := by
  refine ⟨fun hq => ?_, step_bedrock s cmd⟩
  cases hc : s.change cmd with
  | none => rwa [step_get_of_edit_none (by simp [edit, hc])] at hq
  | some c =>
    have he := edit_of_change hc
    by_cases hp : q = c.pos
    · subst hp
      rw [step_get_of_edit he] at hq
      rcases change_cases hc with ⟨-, hair, -, -, -⟩ | ⟨-, -, -, htake⟩
      · rw [hair] at hq
        cases hq
      · exact absurd hq (Inventory.Lacks.take h.bedrock htake).1
    · rwa [step_get_of_ne he hp] at hq

/--
**No jumping in mid-air.** In a sound state, a player who is not flying and has
nothing beneath them at the start of a tick can only fall during it.
-/
theorem Sound.intent_airborne {s : State} (h : s.Sound) (input : Input)
    (hair : Player.blocked s.world.solid (s.player.pos.add .y (-1)) = false)
    (hfly : (s.player.flying != input.toggleFly) = false) :
    (Player.intent input s.player).y
      = max (-Player.maxSpeed) (s.player.vel.y - Player.gravity) :=
  Player.intent_airborne input (h.grounded.trans hair) hfly

/-! ## Only what can be seen matters -/

/--
Two states that cannot be told apart: the same player, inventory and selected
slot, and the same block at every position. Their worlds may still be stored
differently, as a played world and the same world loaded from a file are.
-/
structure Same (s t : State) : Prop where
  player : s.player = t.player
  inventory : s.inventory = t.inventory
  selected : s.selected = t.selected
  world : ∀ p, s.world.get p = t.world.get p

theorem Same.rfl {s : State} : Same s s :=
  ⟨Eq.refl _, Eq.refl _, Eq.refl _, fun _ => Eq.refl _⟩

theorem Same.solid {s t : State} (h : Same s t) : s.world.solid = t.world.solid :=
  funext fun p => by simp only [World.solid, h.world]

/-- States that cannot be told apart answer every command with the same change. -/
theorem Same.change {s t : State} (h : Same s t) (cmd : Command) :
    s.change cmd = t.change cmd := by
  have hg : s.world.get = t.world.get := funext h.world
  simp only [State.change, State.target, State.eye, State.slot, h.solid, hg, h.player,
    h.inventory, h.selected]

/-- A tick keeps them that way. -/
theorem Same.step {s t : State} (h : Same s t) (cmd : Command) :
    Same (s.step cmd) (t.step cmd) := by
  have hc := h.change cmd
  have hworld : ∀ p, (s.step cmd).world.get p = (t.step cmd).world.get p := by
    intro p
    simp only [State.step, hc]
    cases t.change cmd with
    | none => exact h.world p
    | some c => simp only [World.get_set, h.world]
  have hsolid : (s.step cmd).world.solid = (t.step cmd).world.solid :=
    funext fun p => by simp only [World.solid, hworld]
  refine ⟨?_, ?_, ?_, hworld⟩
  · rw [step_player, step_player, hsolid, h.player]
  · rw [step_inventory, step_inventory, hc, h.inventory]
  · rw [step_selected, step_selected, h.selected]

/--
**Only what can be seen matters.** States that cannot be told apart stay that
way under any commands: the game's behaviour depends on a world only through
the block it holds at each position.
-/
theorem Same.run {s t : State} (h : Same s t) (cmds : List Command) :
    Same (s.run cmds) (t.run cmds) := by
  induction cmds generalizing s t with
  | nil => exact h
  | cons cmd cmds ih => exact ih (h.step cmd)

end State

end LeanMc
