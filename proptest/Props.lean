import PropTest.Shrink
import PropTest.Spec
import Basalt.IO

/-!
# Property tests of the pure core

Each property generates wide random inputs with basalt and, on failure, shrinks
them with the hand-written shrinkers. Most restate a theorem and so check the
compiled code against it; the targeting property checks something that is not
proved. The last group are deliberately false properties, which check that the
generators reach the interesting cases and that the shrinkers work.

Run with `lake test`, or `lake exe props --runs N --seed N`.
-/

open LeanMc PropTest

/-! ## Rendering inputs for reports -/

def showCommands (cmds : List Command) : String :=
  s!"{cmds.length} commands: {repr cmds}"

def showFrames (fs : List Frame) : String :=
  s!"{fs.length} frames: {repr fs}"

/-! ## Properties -/

/-- The first way a run of commands leaves the game unsound, if any. -/
def unsoundness (start : State) (cmds : List Command) : Option String := Id.run do
  let mut s := start
  let mut tick := 0
  for cmd in cmds do
    let edit := s.edit cmd
    let next := s.step cmd
    let feet := next.player.pos.blockPos
    if Player.blocked next.world.solid next.player.pos then
      return some s!"tick {tick}: the player is inside a solid block"
    if next.player.pos.y < 65536 then
      return some s!"tick {tick}: the player is below the floor"
    if next.world.get ⟨feet.x, 0, feet.z⟩ != .bedrock then
      return some s!"tick {tick}: the floor is broken"
    let kinds : List Block :=
      [.bedrock, .stone, .dirt, .grass, .sand, .log, .leaves, .planks, .cobble]
    match edit with
    | some (p, b) =>
      if next.world.get p != b then
        return some s!"tick {tick}: the edited cell does not hold the block asked for"
      if s.world.solid p && b != .air then
        return some s!"tick {tick}: a solid block was replaced"
      if let some k := kinds.find? fun k =>
          next.inventory.count k + (if next.world.get p == k then 1 else 0)
            != s.inventory.count k + (if s.world.get p == k then 1 else 0) then
        return some s!"tick {tick}: {repr k} was created or destroyed"
    | none =>
      if kinds.any fun k => next.inventory.count k != s.inventory.count k then
        return some s!"tick {tick}: the inventory changed without an edit"
    if (List.finRange 9).any fun i =>
        match next.inventory.stack i with
        | some stack =>
          stack.count < 1 || stack.count > 64 || stack.block == .air || stack.block == .bedrock
        | none => false then
      return some s!"tick {tick}: a stack is empty, too big, or made of air or bedrock"
    if !decide next.player.SpeedBounded then
      return some s!"tick {tick}: the player is over the speed limit"
    if next.player.onGround
        != Player.blocked next.world.solid (next.player.pos.add .y (-1)) then
      return some s!"tick {tick}: the player is wrong about standing on something"
    if next.entities.length < s.entities.length then
      return some s!"tick {tick}: a fox vanished"
    if (s.entities.zipIdx).any fun (e, i) =>
        !State.loaded s.centre e.chunk && next.entities[i]? != some e then
      return some s!"tick {tick}: a fox in an unloaded chunk changed"
    if (State.loadedColumns next.centre).any fun c => !next.populated.contains c then
      return some s!"tick {tick}: a loaded column has not been populated"
    if next.entities.any fun e => Entity.shape.blocked next.world.solid e.pos then
      return some s!"tick {tick}: a fox is inside a solid block"
    if next.entities.any fun e => e.pos.y < 65536 then
      return some s!"tick {tick}: a fox is below the floor"
    if next.entities.any fun e => !decide e.SpeedBounded then
      return some s!"tick {tick}: a fox is over the speed limit"
    if next.entities.any fun e =>
        e.onGround != Entity.shape.blocked next.world.solid (e.pos.add .y (-1)) then
      return some s!"tick {tick}: a fox is wrong about standing on something"
    if let some (p, _) := edit then
      let eye := s.eye.blockPos
      if (p.x - eye.x).natAbs > 5 || (p.y - eye.y).natAbs > 5 || (p.z - eye.z).natAbs > 5 then
        return some s!"tick {tick}: a block out of reach was changed"
    s := next
    tick := tick + 1
  return none

/-- What the pacing theorems say about a run of frames, checked on the compiled code. -/
def pacingFault (start : Session) (frames : List Frame) : Option String :=
  let (final, cmds) := start.play frames
  let pressed (p : Frame → Bool) := frames.countP p
  let digs := cmds.countP (·.dig)
  let places := cmds.countP (·.place)
  let flips := frames.countP (·.fly)
  if final.debt ≥ unitsPerTick then some "a whole tick of time is still owed"
  else if cmds.any (fun c => c.dig && c.place) then some "a command both digs and places"
  else if digs + final.pending.dig.toNat > pressed (·.dig) then
    some s!"{digs} digs ran for {pressed (·.dig)} presses"
  else if (pressed (·.dig) > 0) != (digs > 0 || final.pending.dig) then
    some s!"dig presses and dig commands disagree: {pressed (·.dig)} pressed, {digs} ran, \
      waiting: {final.pending.dig}"
  else if (pressed (·.place) > 0) != (places > 0 || final.pending.place) then
    some "place presses and place commands disagree"
  else if places + final.pending.place.toNat > pressed (·.place) then
    some s!"{places} placements ran for {pressed (·.place)} presses"
  else if final.selectIntent
      != (frames.foldl (fun chosen f => f.select.getD chosen) start.selectIntent) then
    some "the selected slot is not the most recent one chosen"
  else if final.flyIntent != (start.flyIntent != (flips % 2 == 1)) then
    some s!"{flips} fly presses left the fly mode wrong"
  else if cmds.length * unitsPerTick + final.debt > (frames.map (·.elapsed)).sum + start.debt then
    some "more time was simulated than passed"
  else none

/-- The cells the targeting walk visits along a segment when nothing is in the way. -/
def walkCells (o d : Vec3) : List BlockPos := Id.run do
  let mut c := o.blockPos
  let mut cells := [c]
  for _ in [0:Ray.remaining o d o.blockPos + 1] do
    match Ray.nextStep o d c with
    | none => break
    | some dir =>
      c := c.step dir
      cells := c :: cells
  return cells.reverse

/--
Whether the segment from `o` to `o + d` touches the closed cell `c`, decided
exactly: the stretches of the segment lying within the cell's extent along
each axis must have a point in common.
-/
def touches (o d : Vec3) (c : BlockPos) : Bool :=
  let axis (o d c : Int) : Option (Rat × Rat) :=
    let lo := c * 65536
    let hi := (c + 1) * 65536
    if d = 0 then (if lo ≤ o ∧ o ≤ hi then some (0, 1) else none)
    else
      let a := mkRat (lo - o) d.natAbs * (if d < 0 then -1 else 1)
      let b := mkRat (hi - o) d.natAbs * (if d < 0 then -1 else 1)
      some (min a b, max a b)
  match axis o.x d.x c.x, axis o.y d.y c.y, axis o.z d.z c.z with
  | some x, some y, some z =>
    max (max 0 x.1) (max y.1 z.1) ≤ min (min 1 x.2) (min y.2 z.2)
  | _, _, _ => false

/--
Compare the walk with the geometry, exactly. Every cell walked must be touched
by the segment, and every cell whose inside the segment passes through, at any
of 257 evenly spaced points, must have been walked.
-/
def walkFault (o d : Vec3) : Option String :=
  let cells := walkCells o d
  match cells.find? (!touches o d ·) with
  | some c => some s!"the walk visits {repr c}, which the segment does not touch"
  | none =>
    (List.range 257).findSome? fun (k : Nat) =>
      -- The point k/256 of the way along, scaled by 256 so that it is exact.
      let px := o.x * 256 + d.x * k
      let py := o.y * 256 + d.y * k
      let pz := o.z * 256 + d.z * k
      let scale : Int := 65536 * 256
      let inside := px % scale != 0 && py % scale != 0 && pz % scale != 0
      let c : BlockPos := ⟨px / scale, py / scale, pz / scale⟩
      if inside && !cells.contains c then
        some s!"the segment passes inside {repr c} at {k}/256, but the walk skips it"
      else none

/-- March along a segment in small steps and report the first solid cell. -/
def march (solid : BlockPos → Bool) (o v : Vec3) : Option BlockPos :=
  (List.range 4097).findSome? fun (k : Nat) =>
    let c := (⟨o.x + v.x * k / 4096, o.y + v.y * k / 4096, o.z + v.z * k / 4096⟩ : Vec3).blockPos
    if solid c then some c else none

/-- What a run of renderer operations does to the world, the planner and the model shim. -/
structure RenderRun where
  world : World
  renderer : Renderer := {}
  gpu : Gpu := {}
  /-- The eye of the most recent draw, if the scene is still current. -/
  drawn : Option Vec3 := none
  /-- Every command the planner has sent, oldest first. -/
  sent : Array GpuCmd := #[]

def RenderRun.step (run : RenderRun) : RenderOp → RenderRun
  | .mesh c =>
    let (renderer, cmds) := run.renderer.remesh run.world c
    { run with renderer, gpu := run.gpu.run cmds, drawn := none, sent := run.sent ++ cmds }
  | .edit p b =>
    let world := run.world.set p b
    let (renderer, cmds) := run.renderer.applyEdit world p b
    { run with world, renderer, gpu := run.gpu.run cmds, drawn := none, sent := run.sent ++ cmds }
  | .dropFar centre =>
    let (renderer, cmds) := run.renderer.dropFar ⟨1, 1⟩ centre
    { run with renderer, gpu := run.gpu.run cmds, drawn := none, sent := run.sent ++ cmds }
  | .draw eye =>
    let cmds := run.renderer.drawCmds eye
    { run with gpu := run.gpu.run cmds, drawn := some eye, sent := run.sent ++ cmds }

/-- Every command the planner sends over a run of operations. -/
def sentCommands (ops : List RenderOp) : List GpuCmd :=
  (ops.foldl RenderRun.step { world := Terrain.flatWorld }).sent.toList

/-- Whether some slot is emptied and later filled again. -/
def reusesSlot (cmds : List GpuCmd) : Bool :=
  (cmds.foldl (init := (([] : List Nat), false)) fun (emptied, reused) cmd =>
    match cmd with
    | .unload slot => (slot :: emptied, reused)
    | .upload slot _ => (emptied, reused || emptied.contains slot)
    | _ => (emptied, reused)).2

/--
The first way a planner and a model shim disagree with a world, if any. `drawn`
is the eye of the most recent draw, if the scene is still current.
-/
def syncFault (renderer : Renderer) (world : World) (gpu : Gpu) (drawn : Option Vec3) :
    Option String :=
  let slots := renderer.slots.toList
  let used := (slots.map (·.2)).filter (· != 0)
  if gpu.fault then some "the planner misused the shim"
  else if used.eraseDups.length != used.length then some "two chunks share a slot"
  else if let some (c, _) := slots.find? fun (c, slot) =>
      let mesh := meshChunk world.get c
      if slot = 0 then mesh.size != 0 else gpu.meshes[slot]? != some mesh then
    some s!"chunk {repr c} does not hold the world's mesh"
  else
    match drawn with
    | none => none
    | some eye =>
      let expected := slots.filterMap fun (c, slot) =>
        if slot = 0 then none else some (slot, Renderer.chunkOffset c eye)
      if gpu.scene.length != expected.length
          || !expected.all (gpu.scene.contains ·) then
        some "the scene is not one draw per meshed chunk"
      else none

/-- The first way the planner and the model shim disagree with the world, if any. -/
def renderFault (ops : List RenderOp) : Option String :=
  let run := ops.foldl RenderRun.step { world := Terrain.flatWorld }
  syncFault run.renderer run.world run.gpu run.drawn

/--
What a renderer operation asks of a client. A client has no way to drop a
chunk's mesh at will: meshes go when a game is loaded, so where the renderer
test drops far chunks, the client loads the game as it began.
-/
def clientOp (start : Session) : RenderOp → Client.Op
  | .mesh c => .mesh c
  | .edit p b => .edit p b
  | .dropFar _ => .restart start
  | .draw eye => .draw eye

/--
The steps a client takes for a run: the renderer operations and the frames in
turn, with far chunks unloaded after each frame, as the shell may do.
-/
def clientOps (start : Session) : List RenderOp → List Frame → List Client.Op
  | op :: ops, f :: fs => clientOp start op :: .frame f :: .unloadFar :: clientOps start ops fs
  | ops, [] => ops.map (clientOp start)
  | [], fs => fs.flatMap fun f => [.frame f, .unloadFar]

/--
What `Client.run_synced` says, checked on the compiled code: after any steps,
the planner and the model shim agree with the world the session ended in.
-/
def clientFault (start : Session) (run : List RenderOp × List Frame) : Option String :=
  let ops := clientOps start run.1 run.2
  let (client, cmds) := (Client.start start).run ops
  let drawn := match ops.getLast? with
    | some (.draw eye) => some eye
    | _ => none
  syncFault client.renderer client.world (({} : Gpu).run cmds) drawn

/-- Whether some step of the kind `which` picks out has the client send a command `sent` picks out. -/
def clientSends (start : Session) (which : Client.Op → Bool) (sent : GpuCmd → Bool)
    (run : List RenderOp × List Frame) : Bool :=
  ((clientOps start run.1 run.2).foldl (init := (Client.start start, false)) fun (client, found) op =>
    let step := client.apply op
    (step.1, found || (which op && step.2.any sent))).2

def showClientRun (run : List RenderOp × List Frame) : String :=
  s!"{run.1.length} operations: {repr run.1}, with {showFrames run.2}"

/--
The first generator whose draw falls outside its predicate in `PropTest.Spec`,
if any. `PropTestProofs` proves none can, of the generators as distributions;
this checks the same of what the real random source makes them produce.
-/
def specFault
    (sample : Frame × (UInt64 × List Command) × (Vec3 × Vec3) × SaveData × RenderOp × GpuCmd) :
    Option String :=
  let (frame, seeded, ray, save, op, cmd) := sample
  if !decide (Spec.FrameOK frame) then some "genFrame left its predicate"
  else if !decide (Spec.SeededCommandsOK seeded) then some "genSeededCommands left its predicate"
  else if !decide (Spec.RayOK ray) then some "genRay left its predicate"
  else if !decide (Spec.SaveOK save) then some "genSaveData left its predicate"
  else if !decide (Spec.RenderOpOK op) then some "genRenderOp left its predicate"
  else if !decide (Spec.GpuCmdOK cmd) then some "genGpuCmd left its predicate"
  else none

def parseArgs (runs seed : Nat) : List String → Nat × Nat
  | "--runs" :: n :: rest => parseArgs (n.toNat?.getD runs) seed rest
  | "--seed" :: n :: rest => parseArgs runs (n.toNat?.getD seed) rest
  | _ :: rest => parseArgs runs seed rest
  | [] => (runs, seed)

def main (args : List String) : IO UInt32 := do
  let (runs, seed) := parseArgs 200 (← IO.monoNanosNow) args
  ioGen.set (SplitMix.ofSeed seed.toUInt64)
  IO.println s!"property tests: {runs} runs each, seed {seed}"
  let mut ok := true

  -- Start with blocks in hand so that placing is exercised from the first tick.
  let kit := [(Block.planks, 40), (.cobble, 70), (.sand, 3)].foldl
    (fun inv (b, n) => (List.range n).foldl (fun inv _ => (inv.add b).getD inv) inv)
    ({} : Inventory)
  -- A fox stands two blocks east of the player, where digging and placing can reach it,
  -- and there is another in every eighth column of chunks, to be met and left behind.
  let foxes (cx cz : Int) : List Entity :=
    if cx % 8 == 0 && cz % 8 == 0 then
      [Entity.resting Terrain.flatWorld.solid
        ⟨cx * 1048576 + 425984, 589824, cz * 1048576 + 294912⟩]
    else []
  let some flat := Session.start? (Terrain.flatWorld foxes) Terrain.flatWorld_floor
      (Player.resting Terrain.flatWorld.solid ⟨294912, 589824, 294912⟩) kit
    | IO.println "FAIL  could not start in the flat world"
      return 1
  let flatSolid := Terrain.flatWorld.solid

  ok := (← holds "the generated world stays sound under any commands" (runs / 4)
    genSeededCommands
    (shrinkPair (fun _ => []) (shrinkList shrinkCommand))
    (fun (seed, cmds) => s!"seed {seed}, {showCommands cmds}")
    (fun (seed, cmds) => pure (unsoundness { Terrain.initial seed with inventory := kit } cmds)))
    && ok

  ok := (← holds "the flat world stays sound under any commands" runs
    (genCommands 150) (shrinkList shrinkCommand) showCommands
    (fun cmds => pure (unsoundness flat.state cmds))) && ok

  ok := (← holds "no press is lost, repeated or invented at any frame rate" (runs * 2)
    genFrames (shrinkList shrinkFrame) showFrames
    (fun frames => pure (pacingFault flat frames))) && ok

  ok := (← holds "the targeting walk visits exactly the cells the segment passes through"
    (runs * 5) genRay (shrinkPair shrinkVec3 shrinkVec3) (fun r => s!"{repr r}")
    (fun (o, v) => pure (walkFault o v))) && ok

  ok := (← holds "the target is the first solid cell on that walk" (runs * 5)
    genRay (shrinkPair shrinkVec3 shrinkVec3) (fun r => s!"{repr r}")
    (fun (o, v) => pure <|
      let hit := (Ray.cast flatSolid o v).map (·.block)
      let first := (walkCells o v).find? flatSolid
      if hit == first then none else some s!"cast gave {repr hit}, the walk gives {repr first}")) && ok

  ok := (← holds "the planner keeps the model shim showing the world" (runs / 2)
    genRenderOps (shrinkList shrinkRenderOp)
    (fun ops => s!"{ops.length} operations: {repr ops}")
    (fun ops => pure (renderFault ops))) && ok

  ok := (← holds "a client keeps the model shim showing the session's world" (runs / 2)
    genClientRun (shrinkPair (shrinkList shrinkRenderOp) (shrinkList shrinkFrame)) showClientRun
    (fun run => pure (clientFault flat run))) && ok

  ok := (← holds "any saved game survives being written as text and read back" (runs * 3)
    genSaveData shrinkSaveData (fun d => s!"{repr d}")
    (fun d => pure <|
      if SaveData.decode? d.encode != some d then some "the integers do not decode to it"
      else if SaveData.ofText? d.toText != some d then some "the text does not read back to it"
      else none)) && ok

  -- Change one integer of a valid save: it must be refused or still mean exactly what it says.
  ok := (← holds "a save with one number changed is refused or re-encodes to itself" (runs * 3)
    genMutatedSave
    (shrinkList shrinkInt) (fun ints => s!"{ints}")
    (fun ints => pure <|
      match SaveData.decode? ints with
      | none => none
      | some d => if d.encode == ints then none else some s!"it decodes to {repr d}")) && ok

  ok := (← holds "every generator draws only what it is proved to produce" (runs * 2)
    (do return (← genFrame, ← genSeededCommands, ← genRay, ← genSaveData, ← genRenderOp,
      ← genGpuCmd))
    (fun _ => []) (fun _ => "one draw from each generator") (fun sample => pure (specFault sample)))
    && ok

  -- Deliberately false properties: the tests must be able to fail, and fail small.
  ok := (← refutes "self-check: some saved games do not load" runs
    genSaveData shrinkSaveData (fun d => d.edits.length) 1 (fun d => s!"{repr d}")
    (fun d => pure (if d.restore?.isNone then some "refused" else none))) && ok


  ok := (← refutes "self-check: a dig press can go unanswered within one frame" (runs * 2)
    genFrames (shrinkList shrinkFrame) List.length 1 showFrames
    (fun frames => pure <|
      if frames.any (·.dig) && (flat.play frames).1.pending.dig then some "a dig is waiting"
      else none)) && ok

  ok := (← refutes "self-check: a coarse march disagrees with the walk somewhere" (runs * 20)
    genRay (shrinkPair shrinkVec3 shrinkVec3) (fun _ => 0) 0 (fun r => s!"{repr r}")
    (fun (o, v) => pure <|
      if (Ray.cast flatSolid o v).map (·.block) != march flatSolid o v then some "they differ"
      else none)) && ok

  ok := (← refutes "self-check: commands can change a block" runs
    (genCommands 150) (shrinkList shrinkCommand) List.length 1 showCommands
    (fun cmds => pure <|
      if (flat.state.run cmds).world.edits.size > 0 then some "the world changed" else none)) && ok

  ok := (← refutes "self-check: the planner empties a slot" runs
    genRenderOps (shrinkList shrinkRenderOp) List.length 3
    (fun ops => s!"{repr ops}")
    (fun ops => pure <|
      if (sentCommands ops).any (fun | .unload _ => true | _ => false) then some "a slot was emptied"
      else none)) && ok

  ok := (← refutes "self-check: the planner reuses an emptied slot" (runs * 2)
    genRenderOps (shrinkList shrinkRenderOp) List.length 5
    (fun ops => s!"{repr ops}")
    (fun ops => pure <|
      if reusesSlot (sentCommands ops) then some "an emptied slot was filled again" else none)) && ok

  ok := (← refutes "self-check: a frame of play changes a chunk a client has meshed" runs
    genClientRun (shrinkPair (shrinkList shrinkRenderOp) (shrinkList shrinkFrame))
    (fun run => run.1.length + run.2.length) 3 showClientRun
    (fun run => pure <|
      if clientSends flat (fun | .frame _ => true | _ => false) (fun | .upload .. => true | _ => false)
          run then
        some "a frame had a mesh rebuilt"
      else none)) && ok

  ok := (← refutes "self-check: loading a game empties a client's slots" runs
    genClientRun (shrinkPair (shrinkList shrinkRenderOp) (shrinkList shrinkFrame))
    (fun run => run.1.length + run.2.length) 2 showClientRun
    (fun run => pure <|
      if clientSends flat (fun | .restart _ => true | _ => false) (fun | .unload _ => true | _ => false)
          run then
        some "a load emptied a slot"
      else none)) && ok

  ok := (← refutes "self-check: an edit touches the chunk above or below" runs
    genRenderOps (shrinkList shrinkRenderOp) List.length 1
    (fun ops => s!"{repr ops}")
    (fun ops => pure <|
      if ops.any (fun | .edit p _ => (dirtyChunks p).any (·.y != p.chunkPos.y) | _ => false) then
        some "a chunk above or below is dirty"
      else none)) && ok

  ok := (← refutes "self-check: a dig and a place can wait together, and the place waits a tick" (runs * 2)
    genFrames (shrinkList shrinkFrame) List.length 4 showFrames
    (fun frames => pure <|
      if (flat.play frames).1.pending.place && (flat.play frames).2.any (·.dig) then
        some "a place is waiting behind a dig"
      else none)) && ok

  ok := (← refutes "self-check: an edit at a chunk edge dirties more than one chunk" runs
    genRenderOps (shrinkList shrinkRenderOp) List.length 1
    (fun ops => s!"{repr ops}")
    (fun ops => pure <|
      if ops.any (fun | .edit p _ => (dirtyChunks p).length > 1 | _ => false) then
        some "more than one chunk is dirty"
      else none)) && ok

  return if ok then 0 else 1
