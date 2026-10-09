import LeanMc.Core.Game
import LeanMc.Core.Terrain
import LeanMc.Core.Generated
import LeanMc.Proofs.Game

/-!
# Frames and ticks

The screen redraws at whatever rate the display runs, while the game advances
in fixed ticks. This module is the bridge: given what the input devices
reported during one frame and how long the frame took, it decides how many
ticks to run and what command each one gets.

The delicate part is input that happens at an instant. A key or button going
down is reported in one frame only, and that frame may be too short to contain
a tick. So presses are held in `Pending` until a tick takes them.

A tick digs or places, never both, so a dig and a place that are waiting
together take a tick each: the dig goes first and the place waits for the next
tick, in this frame or a later one. `LeanMc.Proofs.Session` shows that no press
is lost, repeated or invented, and that every one is acted on by a tick of its
own.

Time is counted in whole units of 1/60000 of a second, so a tick is exactly
`unitsPerTick` of them and the bookkeeping is exact.
-/

namespace LeanMc

/-- Time units in one tick. A unit is 1/60000 of a second. -/
def unitsPerTick : Nat := 1000

/-- The most ticks one frame may run, so a long stall cannot snowball. -/
def maxTicksPerFrame : Nat := 15

/-- What the input devices reported during one frame. -/
structure Frame where
  /-- Movement keys held down. Its `toggleFly` is ignored; see `fly`. -/
  move : Input := {}
  /-- From the eyes towards what the player is looking at. -/
  look : Vec3 := ⟨0, 0, 0⟩
  /-- The dig button went down during this frame. -/
  dig : Bool := false
  /-- The place button went down during this frame. -/
  place : Bool := false
  /-- A slot key went down during this frame. -/
  select : Option (Fin 9) := none
  /-- The fly key went down during this frame. -/
  fly : Bool := false
  /-- How long the frame took, in time units. -/
  elapsed : Nat := 0
  deriving Repr

/-- Presses that no tick has acted on yet. -/
structure Pending where
  dig : Bool := false
  place : Bool := false
  /-- The most recent slot chosen. -/
  select : Option (Fin 9) := none
  /-- Whether an odd number of fly presses is waiting. Two presses cancel. -/
  fly : Bool := false
  deriving DecidableEq, Repr

namespace Pending

/-- Take in a frame's presses. The most recent slot chosen wins. -/
def add (p : Pending) (f : Frame) : Pending where
  dig := p.dig || f.dig
  place := p.place || f.place
  select := f.select <|> p.select
  fly := p.fly != f.fly

/-- What the next tick does to the world: a waiting dig first, else a waiting place. -/
def action (p : Pending) : Option Action :=
  if p.dig then some .dig else if p.place then some .place else none

/--
What is still waiting once a tick has run: nothing, unless a dig and a place
were both waiting, in which case the place still is.
-/
def next (p : Pending) : Pending where
  place := p.dig && p.place

/-- What is still waiting after `n` ticks. -/
def after : Nat → Pending → Pending
  | 0, p => p
  | n + 1, p => after n p.next

end Pending

/--
The game together with the bookkeeping that paces it.

A session carries a proof that its state is sound, so one cannot be built or
advanced without that proof: starting the game somewhere bad, or editing the
world behind the rules' back, does not type-check.
-/
structure Session where
  state : State
  sound : state.Sound
  pending : Pending := {}
  /-- Time that has passed but has not yet been simulated; always less than a tick. -/
  debt : Nat := 0
  /-- The seed the world's terrain was generated from, if it was generated from one. -/
  seed : Option UInt64 := none
  /--
  The seed is the truth about the terrain and its creatures, so a saved game
  cannot record the wrong one.
  -/
  seeded : ∀ sd, seed = some sd → state.world.FromSeed sd := by simp

/-- What the shell needs to know about a batch of ticks besides the resulting state. -/
structure RunLog where
  state : State
  /-- Block changes made, oldest first. -/
  edits : Array (BlockPos × Block) := #[]
  /-- Where the player stood before the last tick, if any tick ran. -/
  before : Option Vec3 := none
  /-- The creatures as they were before the last tick, if any tick ran. -/
  entitiesBefore : Option (List Entity) := none

namespace State

/-- Record one tick: step the state and note what it changed. -/
def logStep (log : RunLog) (cmd : Command) : RunLog where
  state := log.state.step cmd
  edits :=
    match log.state.edit cmd with
    | some e => log.edits.push e
    | none => log.edits
  before := some log.state.player.pos
  entitiesBefore := some log.state.entities

/-- `State.run`, also reporting the block changes made along the way. -/
def runLog (s : State) (cmds : List Command) : RunLog :=
  cmds.foldl logStep { state := s }

theorem foldl_logStep_state (cmds : List Command) (log : RunLog) :
    (cmds.foldl logStep log).state = cmds.foldl step log.state := by
  induction cmds generalizing log with
  | nil => rfl
  | cons c cs ih => exact ih _

/-- Logging a run does not change where it ends up. -/
theorem runLog_state (s : State) (cmds : List Command) : (s.runLog cmds).state = s.run cmds :=
  foldl_logStep_state ..

end State

namespace Session

/-- The command for a tick with `p` waiting: held keys, plus the presses this tick acts on. -/
def tickCommand (p : Pending) (f : Frame) : Command where
  move := { f.move with toggleFly := p.fly }
  look := f.look
  action := p.action
  select := p.select

/-- The command for a tick with nothing waiting: held keys only. -/
def heldCommand (f : Frame) : Command where
  move := { f.move with toggleFly := false }
  look := f.look

/-- The commands for `n` ticks of a frame that starts with `p` waiting. -/
def tickCommands (f : Frame) : Nat → Pending → List Command
  | 0, _ => []
  | n + 1, p => tickCommand p f :: tickCommands f n p.next

/-- Whole ticks of time available once this frame's time is added. -/
def ticksOwed (s : Session) (f : Frame) : Nat :=
  (s.debt + f.elapsed) / unitsPerTick

/-- Ticks this frame actually runs. -/
def ticksDue (s : Session) (f : Frame) : Nat :=
  min maxTicksPerFrame (s.ticksOwed f)

/-- The commands this frame's ticks run, in order. -/
def commands (s : Session) (f : Frame) : List Command :=
  tickCommands f (s.ticksDue f) (s.pending.add f)

/--
Presses still waiting after the frame: all of them if no tick ran, and nothing
after two ticks. After exactly one, only a place that gave way to a dig.
-/
def pendingAfter (s : Session) (f : Frame) : Pending :=
  (s.pending.add f).after (s.ticksDue f)

/-- Time still owed after the frame. Time beyond the per-frame limit is dropped. -/
def debtAfter (s : Session) (f : Frame) : Nat :=
  if s.ticksOwed f ≤ maxTicksPerFrame then (s.debt + f.elapsed) % unitsPerTick else 0

/-- Advance the session by one frame. -/
def frame (s : Session) (f : Frame) : Session where
  state := s.state.run (s.commands f)
  sound := s.sound.run _
  pending := s.pendingAfter f
  debt := s.debtAfter f
  seed := s.seed
  seeded sd h :=
    ⟨(State.run_terrain ..).trans (s.seeded sd h).1,
      (State.run_creatures ..).trans (s.seeded sd h).2⟩

/-- `frame`, also reporting what the shell must mirror: block changes and the last move. -/
def frameLog (s : Session) (f : Frame) : Session × RunLog :=
  let log := s.state.runLog (s.commands f)
  ({ state := log.state
     sound := State.runLog_state s.state _ ▸ s.sound.run _
     pending := s.pendingAfter f
     debt := s.debtAfter f
     seed := s.seed
     seeded := fun sd h =>
      State.runLog_state s.state (s.commands f) ▸
        (⟨(State.run_terrain ..).trans (s.seeded sd h).1,
          (State.run_creatures ..).trans (s.seeded sd h).2⟩ :
          (s.state.run (s.commands f)).world.FromSeed sd) }, log)

/-- Advance through a sequence of frames, collecting every command that was run. -/
def play (s : Session) : List Frame → Session × List Command
  | [] => (s, [])
  | f :: fs =>
    let rest := (s.frame f).play fs
    (rest.1, s.commands f ++ rest.2)

/-- The slot that will be selected once waiting presses are acted on. -/
def selectIntent (s : Session) : Fin 9 :=
  s.pending.select.getD s.state.selected

/--
Whether the player will be flying once waiting presses are acted on: the
current mode, flipped if a fly press is waiting.
-/
def flyIntent (s : Session) : Bool :=
  s.state.player.flying != s.pending.fly

end Session

end LeanMc
