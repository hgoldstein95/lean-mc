import LeanMc.Core.Client
import LeanMc.Proofs.Render

/-!
# Client theorems

`LeanMc.Proofs.Render` shows that each thing the planner does keeps it in
agreement with a world and with the model of the graphics side, given the right
world. Here the world is the session's, and the steps are the only ones a
client has.

* **Every step keeps the picture right.** Whatever a client does, the planner
  and the graphics side still agree with the session's world afterwards.
* **So does any run of steps.** From a session's start, after any run of
  meshing, frames, edits, unloading, loading and drawing, they agree. In
  particular no command ever sent is a misuse of the shim.
* **What is drawn is what is there.** After any such run, a frame's scene is
  exactly one draw of the world's mesh for each meshed chunk that has one.

The shell can change a client only by these steps, so this is a statement
about the game as played, given that the shell sends every command it is
handed, in order, and that the real shim behaves like the model.
-/

namespace LeanMc

/-- A session's own block change is a change to that block and no other. -/
theorem Session.edit?_world {s s' : Session} {p : BlockPos} {b : Block}
    (h : s.edit? p b = some s') : s'.state.world = s.state.world.set p b := by
  unfold Session.edit? at h
  split at h
  · cases h
  · simp only [Session.resume?, Option.map_eq_some_iff] at h
    obtain ⟨started, hs, rfl⟩ := h
    split at hs
    · cases hs
      rfl
    · cases hs

namespace Client

/-- The planner and the graphics side `g` agree with the session's world. -/
def Synced (cl : Client) (g : Gpu) : Prop :=
  Renderer.Synced (fun _ => False) cl.renderer cl.world g

/-- A client that has just started agrees with a graphics side holding nothing. -/
theorem Synced.start (session : Session) : (start session).Synced {} :=
  Renderer.Synced.initial _

theorem Synced.mesh {cl : Client} {g : Gpu} (h : cl.Synced g) (c : ChunkPos) :
    (cl.mesh c).1.Synced (g.run (cl.mesh c).2) :=
  (Renderer.Synced.remesh h c).mono fun _ hd => hd.1

theorem Synced.frame {cl : Client} {g : Gpu} (h : cl.Synced g) (f : Frame) :
    (cl.frame f).1.1.Synced (g.run (cl.frame f).1.2) :=
  Renderer.Synced.frame h f

theorem Synced.edit? {cl cl' : Client} {g : Gpu} (h : cl.Synced g) {p : BlockPos} {b : Block}
    {cmds : List GpuCmd} (he : cl.edit? p b = some (cl', cmds)) : cl'.Synced (g.run cmds) := by
  simp only [Client.edit?, Option.map_eq_some_iff, Prod.mk.injEq] at he
  obtain ⟨session, hs, rfl, rfl⟩ := he
  have hw := Session.edit?_world hs
  simp only [Synced, world, hw]
  exact Renderer.Synced.applyEdit h p b

theorem Synced.unloadFar {cl : Client} {g : Gpu} (h : cl.Synced g) :
    cl.unloadFar.1.Synced (g.run cl.unloadFar.2) :=
  Renderer.Synced.dropFar h _ _

theorem Synced.restart {cl : Client} {g : Gpu} (h : cl.Synced g) (session : Session) :
    (cl.restart session).1.Synced (g.run (cl.restart session).2) :=
  Renderer.Synced.reset h _

theorem Synced.draw {cl : Client} {g : Gpu} (h : cl.Synced g) (eye : Vec3) :
    cl.Synced (g.run (cl.draw eye)) :=
  (Renderer.Synced.draw h eye).1

/-- **Every step keeps the picture right.** -/
theorem Synced.apply {cl : Client} {g : Gpu} (h : cl.Synced g) (op : Op) :
    (cl.apply op).1.Synced (g.run (cl.apply op).2) := by
  cases op with
  | mesh c => exact h.mesh c
  | frame f => exact h.frame f
  | edit p b =>
    simp only [Client.apply]
    cases he : cl.edit? p b with
    | none => exact h
    | some step => exact h.edit? he
  | unloadFar => exact h.unloadFar
  | restart session => exact h.restart session
  | draw eye => exact h.draw eye

/-- **So does any run of steps.** -/
theorem Synced.run {cl : Client} {g : Gpu} (h : cl.Synced g) (ops : List Op) :
    (cl.run ops).1.Synced (g.run (cl.run ops).2) := by
  induction ops generalizing cl g with
  | nil => exact h
  | cons op ops ih =>
    simp only [Client.run, Gpu.run_append]
    exact ih (h.apply op)

/--
**The picture is right however the game is played.** Start from any session
with nothing drawn, and take any run of steps. Then the planner and the
graphics side agree with the world the session ended in: every meshed chunk's
slot holds exactly that world's mesh for the chunk, and no two share a slot.
-/
theorem run_synced (session : Session) (ops : List Op) :
    ((start session).run ops).1.Synced (({} : Gpu).run ((start session).run ops).2) :=
  (Synced.start session).run ops

/--
**The shell never misuses the shim.** Nothing a client ever says to send draws
or empties a slot that holds nothing, uploads to a bad slot, or uploads a
malformed mesh.
-/
theorem run_noFault (session : Session) (ops : List Op) :
    (({} : Gpu).run ((start session).run ops).2).fault = false :=
  (run_synced session ops).noFault

/--
**What is drawn is what is there.** Every draw in a frame's scene is some
meshed chunk's slot, placed at that chunk's position, and the slot holds
exactly the mesh of that chunk in the session's world.
-/
theorem Synced.scene_sound {cl : Client} {g : Gpu} (h : cl.Synced g) (eye : Vec3) {s : Nat}
    {offset : Vec3} (hm : (s, offset) ∈ (g.run (cl.draw eye)).scene) :
    ∃ c, cl.renderer.slots[c]? = some s ∧ offset = Renderer.chunkOffset c eye
      ∧ (g.run (cl.draw eye)).meshes[s]? = some (meshChunk cl.world.get c) :=
  Renderer.Synced.scene_sound h eye hm

/--
**Nothing meshed is left out.** Every meshed chunk with something to draw is
drawn; a meshed chunk that is not drawn has an empty mesh.
-/
theorem Synced.scene_complete {cl : Client} {g : Gpu} (h : cl.Synced g) (eye : Vec3)
    {c : ChunkPos} {s : Nat} (hs : cl.renderer.slots[c]? = some s) :
    (s ≠ 0 → (s, Renderer.chunkOffset c eye) ∈ (g.run (cl.draw eye)).scene)
      ∧ (s = 0 → (meshChunk cl.world.get c).size = 0) :=
  Renderer.Synced.scene_complete h eye hs

/-- **Nothing in view is dropped.** Unloading leaves every loaded chunk with the slot it had. -/
theorem slots_unloadFar_of_loaded (cl : Client) {c : ChunkPos}
    (h : State.loaded cl.session.state.centre c = true) :
    cl.unloadFar.1.renderer.slots[c]? = cl.renderer.slots[c]? :=
  Renderer.slots_dropFar_of_contains _ h

end Client

end LeanMc
