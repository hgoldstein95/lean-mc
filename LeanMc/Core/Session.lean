import LeanMc.Core.Game
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
`LeanMc.Proofs.Session` shows that none is lost, repeated or invented.

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
  /-- The place button went down during this frame, with this block selected. -/
  place : Option Block := none
  /-- The fly key went down during this frame. -/
  fly : Bool := false
  /-- How long the frame took, in time units. -/
  elapsed : Nat := 0
  deriving Repr

/-- Presses that no tick has acted on yet. -/
structure Pending where
  dig : Bool := false
  place : Option Block := none
  /-- Whether an odd number of fly presses is waiting. Two presses cancel. -/
  fly : Bool := false
  deriving DecidableEq, Repr

namespace Pending

/-- Take in a frame's presses. The most recent block to place wins. -/
def add (p : Pending) (f : Frame) : Pending where
  dig := p.dig || f.dig
  place := f.place <|> p.place
  fly := p.fly != f.fly

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

/-- What the shell needs to know about a batch of ticks besides the resulting state. -/
structure RunLog where
  state : State
  /-- Block changes made, oldest first. -/
  edits : Array (BlockPos × Block) := #[]
  /-- Where the player stood before the last tick, if any tick ran. -/
  before : Option Vec3 := none

namespace State

/-- Record one tick: step the state and note what it changed. -/
def logStep (log : RunLog) (cmd : Command) : RunLog where
  state := log.state.step cmd
  edits :=
    match log.state.edit cmd with
    | some e => log.edits.push e
    | none => log.edits
  before := some log.state.player.pos

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

/-- The command for the first tick of a frame: held keys plus every waiting press. -/
def firstCommand (p : Pending) (f : Frame) : Command where
  move := { f.move with toggleFly := p.fly }
  look := f.look
  dig := p.dig
  place := p.place

/-- The command for any later tick of the same frame: held keys only. -/
def heldCommand (f : Frame) : Command where
  move := { f.move with toggleFly := false }
  look := f.look

/-- Whole ticks of time available once this frame's time is added. -/
def ticksOwed (s : Session) (f : Frame) : Nat :=
  (s.debt + f.elapsed) / unitsPerTick

/-- Ticks this frame actually runs. -/
def ticksDue (s : Session) (f : Frame) : Nat :=
  min maxTicksPerFrame (s.ticksOwed f)

/-- The commands this frame's ticks run, in order. -/
def commands (s : Session) (f : Frame) : List Command :=
  match s.ticksDue f with
  | 0 => []
  | n + 1 => firstCommand (s.pending.add f) f :: List.replicate n (heldCommand f)

/-- Presses still waiting after the frame: all of them if no tick ran, none otherwise. -/
def pendingAfter (s : Session) (f : Frame) : Pending :=
  if s.ticksDue f = 0 then s.pending.add f else {}

/-- Time still owed after the frame. Time beyond the per-frame limit is dropped. -/
def debtAfter (s : Session) (f : Frame) : Nat :=
  if s.ticksOwed f ≤ maxTicksPerFrame then (s.debt + f.elapsed) % unitsPerTick else 0

/-- Advance the session by one frame. -/
def frame (s : Session) (f : Frame) : Session where
  state := s.state.run (s.commands f)
  sound := s.sound.run _
  pending := s.pendingAfter f
  debt := s.debtAfter f

/-- `frame`, also reporting what the shell must mirror: block changes and the last move. -/
def frameLog (s : Session) (f : Frame) : Session × RunLog :=
  let log := s.state.runLog (s.commands f)
  ({ state := log.state
     sound := State.runLog_state s.state _ ▸ s.sound.run _
     pending := s.pendingAfter f
     debt := s.debtAfter f }, log)

/-- Advance through a sequence of frames, collecting every command that was run. -/
def play (s : Session) : List Frame → Session × List Command
  | [] => (s, [])
  | f :: fs =>
    let rest := (s.frame f).play fs
    (rest.1, s.commands f ++ rest.2)

/--
Whether the player will be flying once waiting presses are acted on: the
current mode, flipped if a fly press is waiting.
-/
def flyIntent (s : Session) : Bool :=
  s.state.player.flying != s.pending.fly

end Session

end LeanMc
