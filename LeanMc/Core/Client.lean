import LeanMc.Core.Start
import LeanMc.Core.Render

/-!
# The game and its picture

A `Client` is a session together with the render planner that draws it. The
two have to change together: the planner's meshes are of the session's world,
so a world that changes without the planner following is drawn wrongly, and a
planner told of changes that did not happen is drawn wrongly too.

So a client cannot be put together from a session and a planner. It starts
from a session with nothing drawn, and after that it changes only by the steps
here. Each step says what to send to the graphics side. The shell holds a
client, takes these steps and sends what they say, and that is all it can do.

`LeanMc.Proofs.Client` shows that every step keeps the planner and the model of
the graphics side in agreement with the session's world, and so that they agree
after any run of steps whatever.
-/

namespace LeanMc

/-- A session and the planner drawing it, which only ever change together. -/
structure Client where
  private mk ::
  session : Session
  renderer : Renderer

namespace Client

/-- Start drawing a session, with nothing meshed yet. -/
def start (session : Session) : Client :=
  ⟨session, {}⟩

def world (cl : Client) : World :=
  cl.session.state.world

/-- Build chunk `c`'s mesh from the world as it is now. -/
def mesh (cl : Client) (c : ChunkPos) : Client × List GpuCmd :=
  let step := cl.renderer.remesh cl.world c
  (⟨cl.session, step.1⟩, step.2)

/--
Advance the game by one frame, the planner following every block change the
frame made. Also gives the frame's log, for whatever else the shell mirrors.
-/
def frame (cl : Client) (f : Frame) : (Client × List GpuCmd) × RunLog :=
  let ran := cl.session.frameLog f
  let followed := cl.renderer.applyEdits cl.world ran.2.edits.toList
  ((⟨ran.1, followed.1⟩, followed.2), ran.2)

/--
Change one block outside the game's rules, the planner following. There is
nothing to do if the session refuses the change.
-/
def edit? (cl : Client) (p : BlockPos) (b : Block) : Option (Client × List GpuCmd) :=
  (cl.session.edit? p b).map fun session =>
    let step := cl.renderer.applyEdit session.state.world p b
    (⟨session, step.1⟩, step.2)

/-- Drop the meshes of chunks well outside what the game has loaded. -/
def unloadFar (cl : Client) : Client × List GpuCmd :=
  let step := cl.renderer.dropFar loadRange cl.session.state.centre
  (⟨cl.session, step.1⟩, step.2)

/-- Take up a different session, as when a game is loaded. Every mesh is of the old world, so all go. -/
def restart (cl : Client) (session : Session) : Client × List GpuCmd :=
  (⟨session, cl.renderer.reset.1⟩, cl.renderer.reset.2)

/-- The commands that draw the world as seen from `eye`. Drawing changes nothing. -/
def draw (cl : Client) (eye : Vec3) : List GpuCmd :=
  cl.renderer.drawCmds eye

/-- One thing the shell can do with a client. -/
inductive Op where
  | mesh (c : ChunkPos)
  | frame (f : Frame)
  | edit (p : BlockPos) (b : Block)
  | unloadFar
  | restart (session : Session)
  | draw (eye : Vec3)

/-- Take one step: the client afterwards, and what to send. -/
def apply (cl : Client) : Op → Client × List GpuCmd
  | .mesh c => cl.mesh c
  | .frame f => (cl.frame f).1
  | .edit p b => (cl.edit? p b).getD (cl, [])
  | .unloadFar => cl.unloadFar
  | .restart session => cl.restart session
  | .draw eye => (cl, cl.draw eye)

/-- Take a run of steps: the client afterwards, and everything sent along the way, in order. -/
def run (cl : Client) : List Op → Client × List GpuCmd
  | [] => (cl, [])
  | op :: ops =>
    let first := cl.apply op
    let rest := first.1.run ops
    (rest.1, first.2 ++ rest.2)

end Client

end LeanMc
