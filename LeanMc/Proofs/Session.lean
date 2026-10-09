import LeanMc.Core.Session
import LeanMc.Proofs.Game

/-!
# Pacing theorems

How frames become ticks, and what happens to input on the way.

* **Every press gets a tick of its own.** A command asks for at most one
  change, so a dig and a place can never share a tick and neither can hide the
  other. When both are waiting the dig runs first and the place runs on the
  very next tick.
* **No press is lost or invented.** Over any sequence of frames, a dig was
  pressed (or was already waiting) exactly when a dig command was run or one is
  still waiting. The same holds for placing.
* **No press is acted on twice.** Within a frame, the dig commands run plus the
  dig still waiting are exactly the digs that were waiting when it began. Over
  any frames they never outnumber the presses. The same holds for placing.
* **A press waits for at most two ticks.** Whenever a frame runs a tick, no dig,
  slot choice or fly press is left waiting, and after two nothing is. Only a
  place that gave way to a dig waits for a second tick.
* **The most recent slot chosen is the one selected**, and **each fly press
  flips the fly mode exactly once**, over any sequence of frames and whether or
  not a tick has run yet.
* **Time is accounted for.** Less than one tick of time is ever owed, and no
  simulated time is invented; none is dropped unless a frame stalls for longer
  than `maxTicksPerFrame` ticks.
* **The edit log is the world's history.** Replaying the block changes a frame
  reports, over the world it started in, gives the world it ended in.
* **Pacing cannot break the game.** A sound state stays sound through any
  sequence of frames, and the terrain and its seed never change.

What these do not cover is the step before: the window library reporting the
press in the first place.
-/

namespace LeanMc

/-- **No command both digs and places**: it has room for one action. -/
theorem Command.not_dig_and_place (c : Command) : ¬ (c.dig = true ∧ c.place = true) := by
  cases h : c.action with
  | none => simp [Command.dig, Command.place, h]
  | some a => cases a <;> simp [Command.dig, Command.place, h]

namespace State

theorem run_append (s : State) (a b : List Command) : s.run (a ++ b) = (s.run a).run b :=
  List.foldl_append ..

theorem step_flying (s : State) (cmd : Command) :
    (s.step cmd).player.flying = (s.player.flying != cmd.move.toggleFly) := rfl

/-- Commands that choose no slot leave the selection alone. -/
theorem run_selected_of_no_select (s : State) (cmds : List Command)
    (h : ∀ c ∈ cmds, c.select = none) : (s.run cmds).selected = s.selected := by
  induction cmds generalizing s with
  | nil => rfl
  | cons c cs ih =>
    have := ih (s.step c) (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    show ((s.step c).run cs).selected = _
    rw [this, step_selected, h c List.mem_cons_self]
    rfl

/-- Commands that carry no fly press leave the fly mode alone. -/
theorem run_flying_of_no_toggle (s : State) (cmds : List Command)
    (h : ∀ c ∈ cmds, c.move.toggleFly = false) :
    (s.run cmds).player.flying = s.player.flying := by
  induction cmds generalizing s with
  | nil => rfl
  | cons c cs ih =>
    have := ih (s.step c) (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))
    show ((s.step c).run cs).player.flying = _
    rw [this, step_flying, h c List.mem_cons_self]
    simp

/-! ## The edit log -/

theorem foldl_logStep_world (cmds : List Command) (log : RunLog) (w : World)
    (h : w.setMany log.edits.toList = log.state.world) :
    w.setMany (cmds.foldl logStep log).edits.toList = (cmds.foldl logStep log).state.world := by
  induction cmds generalizing log with
  | nil => exact h
  | cons c cs ih =>
    apply ih
    simp only [logStep, edit, step]
    cases hc : log.state.change c with
    | none => simpa using h
    | some ch =>
      simp only [Option.map_some, Array.toList_push, World.setMany, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      rw [show List.foldl (fun w e => w.set e.1 e.2) w log.edits.toList = log.state.world from h]

/--
**The edit log is the world's history.** Replaying the block changes a run
reports, in order, over the world it started in, gives exactly the world it
ended in. So whoever mirrors the log, as the renderer does, misses nothing.
-/
theorem runLog_edits (s : State) (cmds : List Command) :
    s.world.setMany (s.runLog cmds).edits.toList = (s.run cmds).world := by
  rw [← runLog_state]
  exact foldl_logStep_world cmds { state := s } s.world rfl

end State

/-! ## What waits, tick by tick -/

namespace Pending

@[simp] theorem next_dig (p : Pending) : p.next.dig = false := rfl
@[simp] theorem next_select (p : Pending) : p.next.select = none := rfl
@[simp] theorem next_fly (p : Pending) : p.next.fly = false := rfl

/-- After a tick, a place is waiting exactly when it gave way to a dig. -/
theorem next_place (p : Pending) : p.next.place = (p.dig && p.place) := rfl

/-- If a dig and a place were not both waiting, one tick takes everything. -/
theorem next_of_not_both {p : Pending} (h : ¬ (p.dig = true ∧ p.place = true)) : p.next = {} := by
  obtain ⟨dig, place, select, fly⟩ := p
  cases dig <;> cases place <;> simp_all [next]

theorem next_next (p : Pending) : p.next.next = {} := rfl

theorem after_empty (n : Nat) : ({} : Pending).after n = {} := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- Two ticks take everything. -/
theorem after_two (n : Nat) (p : Pending) : p.after (n + 2) = {} := by
  show Pending.after n p.next.next = {}
  rw [next_next, after_empty]

/-- With no dig, slot choice or fly press waiting, none appears. -/
theorem after_quiet {p : Pending} (n : Nat) (hd : p.dig = false) (hs : p.select = none)
    (hf : p.fly = false) :
    (p.after n).dig = false ∧ (p.after n).select = none ∧ (p.after n).fly = false := by
  induction n generalizing p with
  | zero => exact ⟨hd, hs, hf⟩
  | succ n ih => exact ih (next_dig p) (next_select p) (next_fly p)

/-- One tick takes every dig, slot choice and fly press. -/
theorem after_succ_quiet (n : Nat) (p : Pending) :
    (p.after (n + 1)).dig = false ∧ (p.after (n + 1)).select = none
      ∧ (p.after (n + 1)).fly = false :=
  after_quiet (p := p.next) n (next_dig p) (next_select p) (next_fly p)

end Pending

namespace Session

/-- The shell's logging variant of `frame` computes the same session. -/
theorem frameLog_fst (s : Session) (f : Frame) : (s.frameLog f).1 = s.frame f := by
  have h := State.runLog_state s.state (s.commands f)
  simp only [frameLog, frame]
  congr 1

/--
**The edit log is the frame's history.** Replaying the block changes a frame
reports over the world it started in gives the world it ended in.
-/
theorem frameLog_edits (s : Session) (f : Frame) :
    s.state.world.setMany (s.frameLog f).2.edits.toList = (s.frame f).state.world :=
  State.runLog_edits s.state (s.commands f)

/-! ## How many ticks, and with what commands -/

theorem tickCommand_empty (f : Frame) : tickCommand {} f = heldCommand f := rfl

/-- A tick digs exactly when a dig is waiting. -/
theorem tickCommand_dig (p : Pending) (f : Frame) : (tickCommand p f).dig = p.dig := by
  obtain ⟨dig, place, select, fly⟩ := p
  cases dig <;> cases place <;> rfl

/-- A tick places exactly when a place is waiting and no dig is ahead of it. -/
theorem tickCommand_place (p : Pending) (f : Frame) :
    (tickCommand p f).place = (!p.dig && p.place) := by
  obtain ⟨dig, place, select, fly⟩ := p
  cases dig <;> cases place <;> rfl

/-- A waiting dig is run by the tick, and no longer waits. -/
theorem tick_dig (p : Pending) (f : Frame) :
    (tickCommand p f).dig.toNat + p.next.dig.toNat = p.dig.toNat := by
  rw [tickCommand_dig]
  simp

/-- A waiting place is either run by the tick or still waits: one or the other, never both. -/
theorem tick_place (p : Pending) (f : Frame) :
    (tickCommand p f).place.toNat + p.next.place.toNat = p.place.toNat := by
  rw [tickCommand_place, Pending.next_place]
  cases p.dig <;> cases p.place <;> rfl

theorem length_tickCommands (f : Frame) (n : Nat) (p : Pending) :
    (tickCommands f n p).length = n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp [tickCommands, ih]

theorem length_commands (s : Session) (f : Frame) : (s.commands f).length = s.ticksDue f :=
  length_tickCommands ..

/-- A count that each tick conserves is conserved by any number of ticks. -/
theorem tickCommands_count (f : Frame) (cmd : Command → Bool) (wait : Pending → Bool)
    (htick : ∀ p, (cmd (tickCommand p f)).toNat + (wait p.next).toNat = (wait p).toNat)
    (n : Nat) (p : Pending) :
    (tickCommands f n p).countP cmd + (wait (p.after n)).toNat = (wait p).toNat := by
  induction n generalizing p with
  | zero => simp [tickCommands, Pending.after]
  | succ n ih =>
    have h1 := ih p.next
    have h2 := htick p
    simp only [tickCommands, Pending.after, List.countP_cons]
    cases hc : cmd (tickCommand p f) <;> simp [hc] at h2 ⊢ <;> omega

theorem mem_tickCommands_quiet {f : Frame} {n : Nat} {p : Pending} {c : Command}
    (hd : p.dig = false) (hs : p.select = none) (hf : p.fly = false)
    (hc : c ∈ tickCommands f n p) :
    c.dig = false ∧ c.select = none ∧ c.move.toggleFly = false := by
  induction n generalizing p with
  | zero => cases hc
  | succ n ih =>
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨(tickCommand_dig p f).trans hd, hs, hf⟩
    · exact ih (Pending.next_dig p) (Pending.next_select p) (Pending.next_fly p) hc

theorem mem_tickCommands_empty {f : Frame} {n : Nat} {c : Command}
    (hc : c ∈ tickCommands f n {}) : c = heldCommand f := by
  induction n with
  | zero => cases hc
  | succ n ih =>
    rcases List.mem_cons.mp hc with rfl | hc
    · rfl
    · exact ih hc

/-- Only the first tick of a frame can dig, choose a slot or toggle flying. -/
theorem tail_commands (s : Session) (f : Frame) {c : Command} (hc : c ∈ (s.commands f).tail) :
    c.dig = false ∧ c.select = none ∧ c.move.toggleFly = false := by
  unfold commands at hc
  cases h : s.ticksDue f with
  | zero => simp [h, tickCommands] at hc
  | succ n =>
    simp only [h, tickCommands, List.tail_cons] at hc
    exact mem_tickCommands_quiet (Pending.next_dig _) (Pending.next_select _)
      (Pending.next_fly _) hc

/-- Only the first two ticks of a frame can carry a press at all; the rest carry held keys alone. -/
theorem drop_two_commands (s : Session) (f : Frame) {c : Command}
    (hc : c ∈ (s.commands f).drop 2) : c = heldCommand f := by
  unfold commands at hc
  match h : s.ticksDue f with
  | 0 => simp [h, tickCommands] at hc
  | 1 => simp [h, tickCommands] at hc
  | n + 2 =>
    simp only [h, tickCommands, List.drop_succ_cons, List.drop_zero, Pending.next_next] at hc
    exact mem_tickCommands_empty hc

theorem ticksDue_pos {s : Session} {f : Frame} (h : unitsPerTick ≤ s.debt + f.elapsed) :
    ∃ n, s.ticksDue f = n + 1 := by
  have hd : s.ticksDue f ≠ 0 := by
    simp only [ticksDue, ticksOwed, unitsPerTick, maxTicksPerFrame] at h ⊢
    omega
  exact Nat.exists_eq_succ_of_ne_zero hd

/--
**A dig, a slot choice and a fly press wait for at most one tick**: once a
tick's worth of time is owed, none of them is left waiting.
-/
theorem frame_pending_quiet {s : Session} {f : Frame} (h : unitsPerTick ≤ s.debt + f.elapsed) :
    (s.frame f).pending.dig = false ∧ (s.frame f).pending.select = none
      ∧ (s.frame f).pending.fly = false := by
  obtain ⟨n, hn⟩ := ticksDue_pos h
  have hp : (s.frame f).pending = (s.pending.add f).after (n + 1) := by
    show Pending.after _ _ = _
    rw [hn]
  rw [hp]
  exact Pending.after_succ_quiet n _

/--
**One tick takes everything, unless a dig and a place are both waiting**, in
which case the dig is run and only the place waits.
-/
theorem frame_pending_cleared_of_not_both {s : Session} {f : Frame}
    (h : unitsPerTick ≤ s.debt + f.elapsed)
    (hb : ¬ ((s.pending.add f).dig = true ∧ (s.pending.add f).place = true)) :
    (s.frame f).pending = {} := by
  obtain ⟨n, hn⟩ := ticksDue_pos h
  show Pending.after _ _ = {}
  rw [hn]
  show Pending.after n (s.pending.add f).next = {}
  rw [Pending.next_of_not_both hb, Pending.after_empty]

/-- **A press waits for at most two ticks**: once two ticks' worth of time is owed, nothing is left waiting. -/
theorem frame_pending_cleared {s : Session} {f : Frame}
    (h : 2 * unitsPerTick ≤ s.debt + f.elapsed) : (s.frame f).pending = {} := by
  have hd : ∃ n, s.ticksDue f = n + 2 := by
    refine ⟨s.ticksDue f - 2, ?_⟩
    simp only [ticksDue, ticksOwed, unitsPerTick, maxTicksPerFrame] at h ⊢
    omega
  obtain ⟨n, hn⟩ := hd
  show Pending.after _ _ = {}
  rw [hn, Pending.after_two]

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

/--
**Every waiting dig is run exactly once.** The dig commands a frame runs, plus
one if a dig is still waiting after it, are exactly the digs waiting when its
ticks began: one, if a dig was waiting or was pressed, and otherwise none.
-/
theorem frame_dig_exact (s : Session) (f : Frame) :
    (s.commands f).countP (·.dig) + (s.frame f).pending.dig.toNat
      = (s.pending.dig || f.dig).toNat :=
  tickCommands_count f (·.dig) (·.dig) (fun p => tick_dig p f) _ _

/-- **Every waiting place is run exactly once**, in the same sense. -/
theorem frame_place_exact (s : Session) (f : Frame) :
    (s.commands f).countP (·.place) + (s.frame f).pending.place.toNat
      = (s.pending.place || f.place).toNat :=
  tickCommands_count f (·.place) (·.place) (fun p => tick_place p f) _ _

theorem frame_dig_count (s : Session) (f : Frame) :
    (s.commands f).countP (·.dig) + (s.frame f).pending.dig.toNat
      ≤ s.pending.dig.toNat + f.dig.toNat := by
  rw [frame_dig_exact]
  cases s.pending.dig <;> cases f.dig <;> decide

theorem frame_place_count (s : Session) (f : Frame) :
    (s.commands f).countP (·.place) + (s.frame f).pending.place.toNat
      ≤ s.pending.place.toNat + f.place.toNat := by
  rw [frame_place_exact]
  cases s.pending.place <;> cases f.place <;> decide

theorem or_iff_of_count {l : List Command} {cmd : Command → Bool} {a b w : Bool}
    (h : l.countP cmd + w.toNat = (a || b).toNat) :
    (a = true ∨ b = true) ↔ (w = true ∨ ∃ c ∈ l, cmd c = true) := by
  rw [← List.countP_pos_iff]
  generalize l.countP cmd = k at h
  cases a <;> cases b <;> cases w <;> simp at h ⊢ <;> omega

theorem frame_dig_iff (s : Session) (f : Frame) :
    (s.pending.dig = true ∨ f.dig = true) ↔
      ((s.frame f).pending.dig = true ∨ ∃ c ∈ s.commands f, c.dig = true) :=
  or_iff_of_count (frame_dig_exact s f)

theorem frame_place_iff (s : Session) (f : Frame) :
    (s.pending.place = true ∨ f.place = true) ↔
      ((s.frame f).pending.place = true ∨ ∃ c ∈ s.commands f, c.place = true) :=
  or_iff_of_count (frame_place_exact s f)

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

/-- What holds of presses frame by frame, in the "lost or invented" sense, holds over any frames. -/
theorem play_iff_of_frame {P : Pending → Prop} {F : Frame → Prop} {C : Command → Prop}
    (hframe : ∀ (s : Session) (f : Frame),
      (P s.pending ∨ F f) ↔ (P (s.frame f).pending ∨ ∃ c ∈ s.commands f, C c))
    (s : Session) (fs : List Frame) :
    (P s.pending ∨ ∃ f ∈ fs, F f) ↔ (P (s.play fs).1.pending ∨ ∃ c ∈ (s.play fs).2, C c) := by
  induction fs generalizing s with
  | nil => simp [play]
  | cons f fs ih =>
    have h1 := hframe s f
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

/-- What bounds the commands run frame by frame bounds them over any frames. -/
theorem play_count_of_frame (cmd : Command → Bool) (wait : Pending → Bool) (press : Frame → Bool)
    (hframe : ∀ (s : Session) (f : Frame),
      (s.commands f).countP cmd + (wait (s.frame f).pending).toNat
        ≤ (wait s.pending).toNat + (press f).toNat)
    (s : Session) (fs : List Frame) :
    (s.play fs).2.countP cmd + (wait (s.play fs).1.pending).toNat
      ≤ (wait s.pending).toNat + fs.countP press := by
  induction fs generalizing s with
  | nil => simp [play]
  | cons f fs ih =>
    have h1 := hframe s f
    have h2 := ih (s.frame f)
    simp only [play, List.countP_append, List.countP_cons]
    cases hf : press f <;> simp [hf] at h1 ⊢ <;> omega

/--
**No dig is lost or invented.** Over any frames, a dig was pressed or already
waiting exactly when a dig command was run or one is still waiting.
-/
theorem play_dig_iff (s : Session) (fs : List Frame) :
    (s.pending.dig = true ∨ ∃ f ∈ fs, f.dig = true) ↔
      ((s.play fs).1.pending.dig = true ∨ ∃ c ∈ (s.play fs).2, c.dig = true) :=
  play_iff_of_frame (P := (·.dig = true)) (F := (·.dig = true)) (C := (·.dig = true))
    frame_dig_iff s fs

/--
**No dig is acted on twice.** The dig commands run, plus one if a dig is still
waiting, never outnumber the dig presses.
-/
theorem play_dig_count (s : Session) (fs : List Frame) :
    (s.play fs).2.countP (·.dig) + (s.play fs).1.pending.dig.toNat
      ≤ s.pending.dig.toNat + fs.countP (·.dig) :=
  play_count_of_frame (·.dig) (·.dig) (·.dig) frame_dig_count s fs

/-- **No placement is lost or invented**, in the same sense as for digging. -/
theorem play_place_iff (s : Session) (fs : List Frame) :
    (s.pending.place = true ∨ ∃ f ∈ fs, f.place = true) ↔
      ((s.play fs).1.pending.place = true ∨ ∃ c ∈ (s.play fs).2, c.place = true) :=
  play_iff_of_frame (P := (·.place = true)) (F := (·.place = true)) (C := (·.place = true))
    frame_place_iff s fs

/-- **No placement is acted on twice**, in the same sense as for digging. -/
theorem play_place_count (s : Session) (fs : List Frame) :
    (s.play fs).2.countP (·.place) + (s.play fs).1.pending.place.toNat
      ≤ s.pending.place.toNat + fs.countP (·.place) :=
  play_count_of_frame (·.place) (·.place) (·.place) frame_place_count s fs

/-! ## Choosing a slot -/

/--
**The most recent slot chosen is the one selected.** Counting a waiting choice
as already made, a frame leaves the selection alone unless a slot key went down
in it, and then selects that slot, however many ticks the frame runs.
-/
theorem frame_selectIntent (s : Session) (f : Frame) :
    (s.frame f).selectIntent = f.select.getD s.selectIntent := by
  cases h : s.ticksDue f with
  | zero =>
    simp only [selectIntent, frame, pendingAfter, commands, h, tickCommands, Pending.after,
      Pending.add, State.run, List.foldl_nil]
    cases f.select <;> rfl
  | succ n =>
    have hrest : ∀ c ∈ tickCommands f n (s.pending.add f).next, c.select = none := fun c hc =>
      (mem_tickCommands_quiet (Pending.next_dig _) (Pending.next_select _)
        (Pending.next_fly _) hc).2.1
    have hrun : (s.state.run (s.commands f)).selected
        = (s.pending.add f).select.getD s.state.selected := by
      simp only [commands, h, tickCommands]
      show ((s.state.step _).run _).selected = _
      rw [State.run_selected_of_no_select _ _ hrest, State.step_selected]
      rfl
    have hpend : (s.frame f).pending.select = none := by
      show (Pending.after _ _).select = none
      rw [h]
      exact (Pending.after_succ_quiet n _).2.1
    simp only [selectIntent, hpend]
    show (s.state.run (s.commands f)).selected = _
    rw [hrun]
    simp only [Pending.add]
    cases f.select <;> rfl

/-- Over any frames: the slot selected, counting a waiting choice, is the last one a key chose. -/
theorem play_selectIntent (s : Session) (fs : List Frame) :
    (s.play fs).1.selectIntent = fs.foldl (fun chosen f => f.select.getD chosen) s.selectIntent := by
  induction fs generalizing s with
  | nil => rfl
  | cons f fs ih =>
    simp only [play, List.foldl_cons]
    rw [ih, frame_selectIntent]

/-! ## The fly key -/

/--
**Each fly press flips the fly mode exactly once.** Counting a waiting press as
already made, a frame changes the fly mode exactly when the key went down in
it, however many ticks the frame runs, including none.
-/
theorem frame_flyIntent (s : Session) (f : Frame) :
    (s.frame f).flyIntent = (s.flyIntent != f.fly) := by
  cases h : s.ticksDue f with
  | zero =>
    simp only [flyIntent, frame, pendingAfter, commands, h, tickCommands, Pending.after,
      Pending.add, State.run, List.foldl_nil]
    cases s.state.player.flying <;> cases s.pending.fly <;> cases f.fly <;> rfl
  | succ n =>
    have hrest : ∀ c ∈ tickCommands f n (s.pending.add f).next, c.move.toggleFly = false :=
      fun c hc => (mem_tickCommands_quiet (Pending.next_dig _) (Pending.next_select _)
        (Pending.next_fly _) hc).2.2
    have hrun : (s.state.run (s.commands f)).player.flying
        = (s.state.player.flying != (s.pending.add f).fly) := by
      simp only [commands, h, tickCommands]
      show ((s.state.step _).run _).player.flying = _
      rw [State.run_flying_of_no_toggle _ _ hrest, State.step_flying]
      rfl
    have hpend : (s.frame f).pending.fly = false := by
      show (Pending.after _ _).fly = false
      rw [h]
      exact (Pending.after_succ_quiet n _).2.2
    simp only [flyIntent, hpend]
    show ((s.state.run (s.commands f)).player.flying != false) = _
    rw [hrun]
    simp only [Pending.add]
    cases s.state.player.flying <;> cases s.pending.fly <;> cases f.fly <;> rfl

/-- Over any frames: the fly mode, counting a waiting press, has flipped once per press. -/
theorem play_flyIntent (s : Session) (fs : List Frame) :
    (s.play fs).1.flyIntent = fs.foldl (fun flying f => flying != f.fly) s.flyIntent := by
  induction fs generalizing s with
  | nil => rfl
  | cons f fs ih =>
    simp only [play, List.foldl_cons]
    rw [ih, frame_flyIntent]

/-! ## Soundness, terrain and seed -/

/--
**Pacing cannot break the game.** A session holds a proof that its state is
sound, and advancing it must produce one, so soundness after any frames is
simply read off the result.
-/
theorem play_sound (s : Session) (fs : List Frame) : (s.play fs).1.state.Sound :=
  (s.play fs).1.sound

/-- Playing never changes the terrain under the edits. -/
theorem play_terrain (s : Session) (fs : List Frame) :
    (s.play fs).1.state.world.terrain = s.state.world.terrain := by
  rw [play_state, State.run_terrain]

/-- Playing never changes the seed a session records. -/
theorem play_seed (s : Session) (fs : List Frame) : (s.play fs).1.seed = s.seed := by
  induction fs generalizing s with
  | nil => rfl
  | cons f fs ih => exact ih (s.frame f)

end Session

end LeanMc
