import LeanMc.Core.Session
import LeanMc.Proofs.Game

/-!
# Pacing theorems

How frames become ticks, and what happens to input on the way.

* **No press is lost or invented.** Over any sequence of frames, a dig was
  pressed (or was already waiting) exactly when a dig command was run or one is
  still waiting. The same holds for placing.
* **No press is acted on twice.** The number of dig commands run, plus one if a
  dig is still waiting, never exceeds the number of dig presses.
* **A press waits for at most one tick.** Whenever a frame runs a tick, the
  first tick carries every waiting press and nothing is left waiting. Later
  ticks of the same frame carry only held keys.
* **Each fly press flips the fly mode exactly once**, whether or not a tick has
  run yet.
* **Time is accounted for.** Less than one tick of time is ever owed, and no
  simulated time is invented; none is dropped unless a frame stalls for longer
  than `maxTicksPerFrame` ticks.
* **Pacing cannot break the game.** A sound state stays sound through any
  sequence of frames.

What these do not cover is the step before: the window library reporting the
press in the first place.
-/

namespace LeanMc

namespace State

theorem run_append (s : State) (a b : List Command) : s.run (a ++ b) = (s.run a).run b :=
  List.foldl_append ..

theorem step_flying (s : State) (cmd : Command) :
    (s.step cmd).player.flying = (s.player.flying != cmd.move.toggleFly) := rfl

end State

namespace Session

/-- The shell's logging variant of `frame` computes the same session. -/
theorem frameLog_fst (s : Session) (f : Frame) : (s.frameLog f).1 = s.frame f := by
  have h := State.runLog_state s.state (s.commands f)
  simp only [frameLog, frame]
  congr 1

/-! ## How many ticks, and with what commands -/

theorem commands_of_no_tick {s : Session} {f : Frame} (h : s.ticksDue f = 0) :
    s.commands f = [] ∧ (s.frame f).pending = s.pending.add f := by
  simp [commands, frame, pendingAfter, h]

theorem commands_of_tick {s : Session} {f : Frame} {n : Nat} (h : s.ticksDue f = n + 1) :
    s.commands f = firstCommand (s.pending.add f) f :: List.replicate n (heldCommand f)
      ∧ (s.frame f).pending = {} := by
  simp [commands, frame, pendingAfter, h]

theorem length_commands (s : Session) (f : Frame) : (s.commands f).length = s.ticksDue f := by
  cases h : s.ticksDue f with
  | zero => simp [(commands_of_no_tick h).1]
  | succ n => simp [(commands_of_tick h).1]

/-- Only the first tick of a frame can carry a press; the rest carry held keys alone. -/
theorem tail_commands (s : Session) (f : Frame) {c : Command} (hc : c ∈ (s.commands f).tail) :
    c.dig = false ∧ c.place = false ∧ c.select = none ∧ c.move.toggleFly = false := by
  cases h : s.ticksDue f with
  | zero => simp [(commands_of_no_tick h).1] at hc
  | succ n =>
    simp only [(commands_of_tick h).1, List.tail_cons] at hc
    rw [List.eq_of_mem_replicate hc]
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- **A press waits for at most one tick**: once a tick's worth of time is owed, nothing is left waiting. -/
theorem frame_pending_cleared {s : Session} {f : Frame}
    (h : unitsPerTick ≤ s.debt + f.elapsed) : (s.frame f).pending = {} := by
  have hd : s.ticksDue f ≠ 0 := by
    simp only [ticksDue, ticksOwed, unitsPerTick, maxTicksPerFrame] at h ⊢
    omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hd
  exact (commands_of_tick hn).2

/-! ## Time -/

/-- Less than one tick of time is ever owed. -/
theorem debt_lt (s : Session) (f : Frame) : (s.frame f).debt < unitsPerTick := by
  simp only [frame, debtAfter, unitsPerTick]
  split <;> omega

/-- Simulated time never exceeds real time. -/
theorem time_not_invented (s : Session) (f : Frame) :
    unitsPerTick * (s.commands f).length + (s.frame f).debt ≤ s.debt + f.elapsed := by
  rw [length_commands]
  by_cases h : s.ticksOwed f ≤ maxTicksPerFrame
  · simp only [frame, debtAfter, h, ↓reduceIte, ticksDue]
    simp only [ticksOwed, unitsPerTick, maxTicksPerFrame] at h ⊢
    omega
  · simp only [frame, debtAfter, h, ↓reduceIte, ticksDue]
    simp only [ticksOwed, unitsPerTick, maxTicksPerFrame] at h ⊢
    omega

/-- Unless a frame stalls past the limit, every unit of time is simulated or carried over. -/
theorem time_accounted (s : Session) (f : Frame) (h : s.ticksOwed f ≤ maxTicksPerFrame) :
    unitsPerTick * (s.commands f).length + (s.frame f).debt = s.debt + f.elapsed := by
  rw [length_commands]
  simp only [frame, debtAfter, h, ↓reduceIte, ticksDue]
  simp only [ticksOwed, unitsPerTick, maxTicksPerFrame] at h ⊢
  omega

/-! ## Presses, one frame at a time -/

theorem frame_dig_iff (s : Session) (f : Frame) :
    (s.pending.dig = true ∨ f.dig = true) ↔
      ((s.frame f).pending.dig = true ∨ ∃ c ∈ s.commands f, c.dig = true) := by
  cases h : s.ticksDue f with
  | zero => simp [(commands_of_no_tick h).1, (commands_of_no_tick h).2, Pending.add]
  | succ n =>
    simp [(commands_of_tick h).1, (commands_of_tick h).2, Pending.add, firstCommand, heldCommand]

theorem frame_dig_count (s : Session) (f : Frame) :
    (s.commands f).countP (·.dig) + (s.frame f).pending.dig.toNat
      ≤ s.pending.dig.toNat + f.dig.toNat := by
  cases h : s.ticksDue f with
  | zero =>
    simp only [(commands_of_no_tick h).1, (commands_of_no_tick h).2, Pending.add, List.countP_nil]
    cases s.pending.dig <;> cases f.dig <;> decide
  | succ n =>
    have hheld : (List.replicate n (heldCommand f)).countP (·.dig) = 0 := by
      rw [List.countP_eq_zero]
      intro c hc
      rw [List.eq_of_mem_replicate hc]
      simp [heldCommand]
    simp only [(commands_of_tick h).1, (commands_of_tick h).2, List.countP_cons, hheld,
      firstCommand, Pending.add]
    cases s.pending.dig <;> cases f.dig <;> simp

theorem frame_place_iff (s : Session) (f : Frame) :
    (s.pending.place = true ∨ f.place = true) ↔
      ((s.frame f).pending.place = true ∨ ∃ c ∈ s.commands f, c.place = true) := by
  cases h : s.ticksDue f with
  | zero => simp [(commands_of_no_tick h).1, (commands_of_no_tick h).2, Pending.add]
  | succ n =>
    simp [(commands_of_tick h).1, (commands_of_tick h).2, Pending.add, firstCommand, heldCommand]

/-! ## Presses, over any sequence of frames -/

theorem exists_mem_append {α : Type} {p : α → Prop} {a b : List α} :
    (∃ x ∈ a ++ b, p x) ↔ (∃ x ∈ a, p x) ∨ ∃ x ∈ b, p x := by
  simp only [List.mem_append]
  constructor
  · rintro ⟨x, hx | hx, hp⟩
    · exact .inl ⟨x, hx, hp⟩
    · exact .inr ⟨x, hx, hp⟩
  · rintro (⟨x, hx, hp⟩ | ⟨x, hx, hp⟩)
    · exact ⟨x, .inl hx, hp⟩
    · exact ⟨x, .inr hx, hp⟩

theorem exists_mem_cons {α : Type} {p : α → Prop} {a : α} {l : List α} :
    (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x := by
  simp

/-- The state after a sequence of frames is the state after running their commands. -/
theorem play_state (s : Session) (fs : List Frame) :
    (s.play fs).1.state = s.state.run (s.play fs).2 := by
  induction fs generalizing s with
  | nil => rfl
  | cons f fs ih =>
    simp only [play, State.run_append]
    exact ih (s.frame f)

/--
**No dig is lost or invented.** Over any frames, a dig was pressed or already
waiting exactly when a dig command was run or one is still waiting.
-/
theorem play_dig_iff (s : Session) (fs : List Frame) :
    (s.pending.dig = true ∨ ∃ f ∈ fs, f.dig = true) ↔
      ((s.play fs).1.pending.dig = true ∨ ∃ c ∈ (s.play fs).2, c.dig = true) := by
  induction fs generalizing s with
  | nil => simp [play]
  | cons f fs ih =>
    have h1 := frame_dig_iff s f
    have h2 := ih (s.frame f)
    simp only [play, exists_mem_append, exists_mem_cons]
    constructor
    · rintro (h | h | h)
      · rcases h1.mp (.inl h) with h | h
        · rcases h2.mp (.inl h) with h | h
          · exact .inl h
          · exact .inr (.inr h)
        · exact .inr (.inl h)
      · rcases h1.mp (.inr h) with h | h
        · rcases h2.mp (.inl h) with h | h
          · exact .inl h
          · exact .inr (.inr h)
        · exact .inr (.inl h)
      · rcases h2.mp (.inr h) with h | h
        · exact .inl h
        · exact .inr (.inr h)
    · rintro (h | h | h)
      · rcases h2.mpr (.inl h) with h | h
        · rcases h1.mpr (.inl h) with h | h
          · exact .inl h
          · exact .inr (.inl h)
        · exact .inr (.inr h)
      · rcases h1.mpr (.inr h) with h | h
        · exact .inl h
        · exact .inr (.inl h)
      · rcases h2.mpr (.inr h) with h | h
        · rcases h1.mpr (.inl h) with h | h
          · exact .inl h
          · exact .inr (.inl h)
        · exact .inr (.inr h)

/--
**No dig is acted on twice.** The dig commands run, plus one if a dig is still
waiting, never outnumber the dig presses.
-/
theorem play_dig_count (s : Session) (fs : List Frame) :
    (s.play fs).2.countP (·.dig) + (s.play fs).1.pending.dig.toNat
      ≤ s.pending.dig.toNat + fs.countP (·.dig) := by
  induction fs generalizing s with
  | nil => simp [play]
  | cons f fs ih =>
    have h1 := frame_dig_count s f
    have h2 := ih (s.frame f)
    simp only [play, List.countP_append, List.countP_cons]
    cases hf : f.dig <;> simp [hf] at h1 ⊢ <;> omega

/-- **No placement is lost or invented**, in the same sense as for digging. -/
theorem play_place_iff (s : Session) (fs : List Frame) :
    (s.pending.place = true ∨ ∃ f ∈ fs, f.place = true) ↔
      ((s.play fs).1.pending.place = true ∨ ∃ c ∈ (s.play fs).2, c.place = true) := by
  induction fs generalizing s with
  | nil => simp [play]
  | cons f fs ih =>
    have h1 := frame_place_iff s f
    have h2 := ih (s.frame f)
    simp only [play, exists_mem_append, exists_mem_cons]
    constructor
    · rintro (h | h | h)
      · rcases h1.mp (.inl h) with h | h
        · rcases h2.mp (.inl h) with h | h
          · exact .inl h
          · exact .inr (.inr h)
        · exact .inr (.inl h)
      · rcases h1.mp (.inr h) with h | h
        · rcases h2.mp (.inl h) with h | h
          · exact .inl h
          · exact .inr (.inr h)
        · exact .inr (.inl h)
      · rcases h2.mp (.inr h) with h | h
        · exact .inl h
        · exact .inr (.inr h)
    · rintro (h | h | h)
      · rcases h2.mpr (.inl h) with h | h
        · rcases h1.mpr (.inl h) with h | h
          · exact .inl h
          · exact .inr (.inl h)
        · exact .inr (.inr h)
      · rcases h1.mpr (.inr h) with h | h
        · exact .inl h
        · exact .inr (.inl h)
      · rcases h2.mpr (.inr h) with h | h
        · rcases h1.mpr (.inl h) with h | h
          · exact .inl h
          · exact .inr (.inl h)
        · exact .inr (.inr h)

/-! ## Choosing a slot -/

theorem run_held_selected (s : State) (f : Frame) (n : Nat) :
    (s.run (List.replicate n (heldCommand f))).selected = s.selected := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, State.run, List.foldl_cons]
    have := ih (s.step (heldCommand f))
    simp only [State.run] at this
    rw [this, State.step_selected]
    rfl

/--
**The most recent slot chosen is the one selected.** Counting a waiting choice
as already made, a frame leaves the selection alone unless a slot key went down
in it, and then selects that slot, however many ticks the frame runs.
-/
theorem frame_selectIntent (s : Session) (f : Frame) :
    (s.frame f).selectIntent = f.select.getD s.selectIntent := by
  cases h : s.ticksDue f with
  | zero =>
    simp only [selectIntent, frame, pendingAfter, h, (commands_of_no_tick h).1, Pending.add,
      State.run, List.foldl_nil, ↓reduceIte]
    cases f.select <;> rfl
  | succ n =>
    have hrun : (s.state.run (s.commands f)).selected = (s.pending.add f).select.getD s.state.selected := by
      rw [(commands_of_tick h).1]
      show ((s.state.step _).run _).selected = _
      rw [run_held_selected, State.step_selected]
      rfl
    simp only [selectIntent, frame, pendingAfter, h, hrun, Pending.add]
    cases f.select <;> rfl

/-! ## The fly key -/

theorem run_held_flying (s : State) (f : Frame) (n : Nat) :
    (s.run (List.replicate n (heldCommand f))).player.flying = s.player.flying := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, State.run, List.foldl_cons]
    have := ih (s.step (heldCommand f))
    simp only [State.run] at this
    rw [this, State.step_flying]
    simp [heldCommand]

/--
**Each fly press flips the fly mode exactly once.** Counting a waiting press as
already made, a frame changes the fly mode exactly when the key went down in
it, however many ticks the frame runs, including none.
-/
theorem frame_flyIntent (s : Session) (f : Frame) :
    (s.frame f).flyIntent = (s.flyIntent != f.fly) := by
  cases h : s.ticksDue f with
  | zero =>
    simp only [flyIntent, frame, pendingAfter, h, (commands_of_no_tick h).1, Pending.add,
      State.run, List.foldl_nil, ↓reduceIte]
    cases s.state.player.flying <;> cases s.pending.fly <;> cases f.fly <;> rfl
  | succ n =>
    have hrun : (s.state.run (s.commands f)).player.flying
        = (s.state.player.flying != (s.pending.add f).fly) := by
      rw [(commands_of_tick h).1]
      show ((s.state.step _).run _).player.flying = _
      rw [run_held_flying, State.step_flying]
      rfl
    simp only [flyIntent, frame, pendingAfter, h, hrun, Pending.add]
    cases s.state.player.flying <;> cases s.pending.fly <;> cases f.fly <;> rfl

/-! ## Soundness -/

/--
**Pacing cannot break the game.** A session holds a proof that its state is
sound, and advancing it must produce one, so soundness after any frames is
simply read off the result.
-/
theorem play_sound (s : Session) (fs : List Frame) : (s.play fs).1.state.Sound :=
  (s.play fs).1.sound

end Session

end LeanMc
