import LeanMc.Core.Game
import LeanMc.Proofs.Ray
import LeanMc.Proofs.Player

/-!
# Game theorems

* **One edit per tick, within reach.** A tick changes at most one block, and
  that block is within six blocks of the player's eyes along every axis.
* **Nothing is overwritten.** A solid block is only ever left alone or removed;
  placing never replaces one.
* **Bedrock is permanent.**
* **The player is never buried.** Neither digging nor placing nor moving puts
  the player inside a solid block.
* **Soundness is an invariant.** Together: starting from a sound state, every
  state reachable by any sequence of commands is sound.
-/

namespace LeanMc.State

/-! ## What an edit can be -/

/--
Every edit is one of two kinds: removing a solid block that is not bedrock, or
filling an empty cell the player is not standing in.
-/
theorem edit_cases {s : State} {cmd : Command} {p : BlockPos} {b : Block}
    (h : s.edit cmd = some (p, b)) :
    (b = .air ∧ s.world.solid p = true ∧ s.world.get p ≠ .bedrock) ∨
      (s.world.solid p = false ∧ ¬ (Player.box s.player.pos).Overlaps p) := by
  unfold edit at h
  split at h
  · cases h
  · next hit ht =>
    split at h
    · split at h
      · cases h
      · next hb =>
        cases h
        exact .inl ⟨rfl, Ray.cast_solid ht, hb⟩
    · split at h
      · next blk f hp hf =>
        split at h
        · cases h
        · next ho =>
          cases h
          exact .inr ⟨Ray.cast_face_clear ht hf, ho⟩
      · cases h

/-- The cell an edit touches is within six blocks of the eyes along every axis. -/
theorem edit_near {s : State} {cmd : Command} {p : BlockPos} {b : Block}
    (h : s.edit cmd = some (p, b)) :
    (p.x - s.eye.blockPos.x).natAbs ≤ 6 ∧ (p.y - s.eye.blockPos.y).natAbs ≤ 6
      ∧ (p.z - s.eye.blockPos.z).natAbs ≤ 6 := by
  have hx := Player.clamp_bounds (lo := -reach) (hi := reach) (by decide) cmd.look.x
  have hy := Player.clamp_bounds (lo := -reach) (hi := reach) (by decide) cmd.look.y
  have hz := Player.clamp_bounds (lo := -reach) (hi := reach) (by decide) cmd.look.z
  unfold edit at h
  split at h
  · cases h
  · next hit ht =>
    have hw := Ray.cast_within ht
    simp only [Ray.Within, reachVector, reach, Vec3.blockPos] at hw hx hy hz ⊢
    split at h
    · split at h
      · cases h
      · cases h
        omega
    · split at h
      · next blk f hp hf =>
        split at h
        · cases h
        · cases h
          cases f <;> simp only [BlockPos.step] <;> omega
      · cases h

/-! ## What a tick does to the world -/

theorem step_world (s : State) (cmd : Command) :
    (s.step cmd).world =
      match s.edit cmd with
      | some (p, b) => s.world.set p b
      | none => s.world := rfl

theorem step_get_of_edit_none {s : State} {cmd : Command} (h : s.edit cmd = none) (q : BlockPos) :
    (s.step cmd).world.get q = s.world.get q := by
  rw [step_world, h]

theorem step_get_of_ne {s : State} {cmd : Command} {p q : BlockPos} {b : Block}
    (h : s.edit cmd = some (p, b)) (hq : q ≠ p) : (s.step cmd).world.get q = s.world.get q := by
  rw [step_world, h]
  exact World.get_set_of_ne _ _ hq

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
      · right
        rw [step_world, h]
        exact World.get_set_self ..
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
      · simp [World.solid, step_world, he, World.get_set_self, Block.isSolid]
      · exact absurd hq ho
    · simp only [World.solid, step_get_of_ne he hp]
      exact h q hq

/-- **The player is never buried.** A tick, edit and movement together, keeps the player free. -/
theorem step_free {s : State} (cmd : Command) (h : Player.Free s.world.solid s.player.pos) :
    Player.Free (s.step cmd).world.solid (s.step cmd).player.pos :=
  Player.step_free cmd.move (free_after_edit cmd h)

/-! ## Soundness as an invariant -/

/-- A state in which nothing has gone wrong. -/
structure Sound (s : State) : Prop where
  /-- The player is not inside a solid block. -/
  free : Player.Free s.world.solid s.player.pos
  /-- The bedrock floor is intact. -/
  floor : ∀ x z, s.world.get ⟨x, 0, z⟩ = .bedrock
  /-- The player's feet are above the floor. -/
  above : 65536 ≤ s.player.pos.y

theorem Sound.step {s : State} (h : Sound s) (cmd : Command) : Sound (s.step cmd) where
  free := step_free cmd h.free
  floor x z := step_bedrock s cmd (h.floor x z)
  above :=
    Player.step_above_floor
      (fun x z => by
        show ((s.step cmd).world.get ⟨x, 0, z⟩).isSolid = true
        rw [step_bedrock s cmd (h.floor x z)]
        rfl)
      cmd.move h.above

/--
**Soundness is an invariant.** From a sound state, no sequence of commands,
however long or adversarial, buries the player, breaks the floor or drops the
player through it.
-/
theorem Sound.run {s : State} (h : Sound s) (cmds : List Command) : Sound (s.run cmds) := by
  induction cmds generalizing s with
  | nil => exact h
  | cons cmd cmds ih => exact ih (h.step cmd)

end LeanMc.State
