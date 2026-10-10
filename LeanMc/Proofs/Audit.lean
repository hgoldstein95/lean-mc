import Lean
import LeanMc.Proofs.Pos
import LeanMc.Proofs.Chunk
import LeanMc.Proofs.World
import LeanMc.Proofs.Terrain
import LeanMc.Proofs.Mesh
import LeanMc.Proofs.Body
import LeanMc.Proofs.Player
import LeanMc.Proofs.Entity
import LeanMc.Proofs.Ray
import LeanMc.Proofs.RayGeometry
import LeanMc.Proofs.Inventory
import LeanMc.Proofs.Game
import LeanMc.Proofs.Session
import LeanMc.Proofs.View
import LeanMc.Proofs.Render
import LeanMc.Proofs.Client
import LeanMc.Proofs.Save
import LeanMc.Core.Start
import LeanMc.Proofs.Generated

/-!
# Axiom audit

Every theorem in the project, checked to rest on nothing but Lean's three
standard axioms. In particular this rules out `sorry` and `native_decide`.
Building this module is the check: a violation is a build error.

There are two checks. The sweep at the end covers every theorem declared in any
`LeanMc.*` module this one imports, so a theorem added later is checked without
anyone remembering to list it; it also fails if a proof module exists that is
not imported here. The lists before it name the headline theorems, so that
renaming or deleting one of those is a build error too.
-/

open Lean Elab Command in
/-- Fail unless each named theorem depends only on Lean's standard axioms. -/
elab "#assert_standard_axioms " ids:ident+ : command => do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for id in ids do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    for ax in ← collectAxioms name do
      unless allowed.contains ax do
        throwErrorAt id "{name} depends on the non-standard axiom {ax}"

open Lean Elab Command in
/--
Fail unless every theorem declared in an imported module whose name starts with
`root` depends only on Lean's standard axioms, and unless every `.lean` file
under `dir` is among those modules.
-/
elab "#assert_all_standard_axioms " root:ident dir:str : command => do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let rootName := root.getId
  let theorems : Array Name := env.constants.fold (init := #[]) fun acc n ci =>
    match ci, env.getModuleIdxFor? n with
    | .thmInfo _, some idx =>
      if rootName.isPrefixOf env.header.moduleNames[idx.toNat]! then acc.push n else acc
    | _, _ => acc
  if theorems.isEmpty then
    throwErrorAt root "no theorems found in modules under {rootName}"
  for n in theorems do
    for ax in ← collectAxioms n do
      unless allowed.contains ax do
        throwErrorAt root "{n} depends on the non-standard axiom {ax}"
  -- Every proof module on disk must be one of the modules swept.
  let imported := env.header.moduleNames.map (·.toString)
  for entry in ← (System.FilePath.mk dir.getString).readDir do
    if entry.path.extension == some "lean" then
      let stem := (entry.fileName.dropEnd 5).toString
      let mod := s!"{dir.getString.replace "/" "."}.{stem}"
      unless imported.contains mod || mod == (← getMainModule).toString do
        throwErrorAt dir "{mod} is not imported by the audit, so its theorems are not checked"
  logInfo m!"{theorems.size} theorems under {rootName} rest on the standard axioms only"

open LeanMc

-- Coordinates
#assert_standard_axioms
  BlockPos.blockAt_chunkPos_localPos
  ChunkPos.chunkPos_blockAt
  ChunkPos.localPos_blockAt
  ChunkPos.blockAt_inj
  LocalPos.ofIndex_index
  LocalPos.index_ofIndex

-- Chunk storage
#assert_standard_axioms
  Chunk.get_set
  Chunk.get_ofFn
  Chunk.ext_get

-- World storage
#assert_standard_axioms
  World.get_set
  World.get_set_set
  World.get_set_comm
  World.get_setMany_new
  World.get_chunk
  World.chunk_set

-- Chunk cache
#assert_standard_axioms
  ChunkCache.valid_empty
  ChunkCache.Valid.blockAt_eq
  ChunkCache.Valid.load
  ChunkCache.Valid.unload
  ChunkCache.Valid.setBlock
  ChunkCache.Valid.blockAt_load_unload

-- Terrain
#assert_standard_axioms
  Terrain.height_bounds
  Terrain.generateChunk_get
  Terrain.generate_bedrock
  Terrain.generate_below
  Terrain.generate_above
  Terrain.generate_isSolid_of_le_height
  Terrain.generate_surface_isSolid

-- Meshing
#assert_standard_axioms
  Dir.corner_on_face
  Dir.winding
  Dir.uv_upright
  size_meshChunk_le
  mem_chunkFaces
  face_mem_chunkFaces
  nodup_chunkFaces
  chunkFaces_congr
  meshChunk_cache
  chunkFaces_set
  meshChunk_set
  toList_packFaces
  size_meshChunk
  Face.toNat_vertex

-- The generated world
#assert_standard_axioms
  Terrain.world_chunk_get
  Terrain.world_setMany_get
  Terrain.mem_chunkFaces_cache

-- Body physics, for any shape
#assert_standard_axioms
  Box.collides_eq_false_iff
  Shape.free_between
  Shape.SafeStep.free_between
  Shape.move_reach
  Shape.move_free
  Shape.move_above_floor
  Shape.move_speedBounded
  Shape.move_shift
  Shape.contact_free
  Shape.moveAxis_flush
  Shape.moveAxis_of_not_blocked
  Shape.moveAxis_flush_of_speed
  Shape.settle_free
  Shape.settle_grounded

-- Player physics
#assert_standard_axioms
  Player.step_reach
  Player.step_free
  Player.step_onGround
  Player.step_above_floor
  Player.step_shift
  Player.step_speedBounded
  Player.intent_airborne
  Terrain.spawn_grounded
  Terrain.initial_onGround
  World.step_translate
  Terrain.generate_above_column
  Terrain.spawn_free
  Terrain.step_above_bedrock

-- Creatures
#assert_standard_axioms
  Entity.think_toBody
  Entity.step_sound
  Entity.stepAll_sound
  Entity.stepAll_length
  Entity.stepAll_asleep
  Terrain.creatures_sound
  Terrain.creatures_column
  Terrain.creatures_length
  Terrain.creatures_filter

-- Loading: what is live, and what is made when
#assert_standard_axioms
  State.step_asleep
  State.step_entities_length
  State.edit_clear_of_unloaded
  State.populate_entities
  State.populate_populated
  State.populate_of_populated
  State.Populated.step
  State.Populated.run
  State.step_populated_mono
  Terrain.initial_populated
  Terrain.play_populated

-- Targeting
#assert_standard_axioms
  Ray.cast_solid
  Ray.cast_face_clear
  Ray.cast_walk
  Ray.cast_within
  Ray.cast_face_within
  Ray.cast_face_none
  Ray.cast_none
  Ray.cast_path
  Ray.cast_touches
  Ray.cast_timed
  Ray.cast_none_path
  Ray.Path.walk

-- The game
#assert_standard_axioms
  State.reachVector_bounds
  State.reachVector_of_within
  State.reachVector_of_long
  State.target_path
  State.target_touches
  State.run_conserves
  State.step_noBedrock
  State.Sound.target_face
  State.Sound.edit_place
  State.Sound.step_bedrock_iff
  State.Sound.intent_airborne
  State.Same.step
  State.Same.run
  State.edit_cases
  State.edit_near
  State.step_changes_at_most_one
  State.step_solid_unchanged_or_air
  State.step_bedrock
  State.change_cases
  State.step_conserves_cell
  State.step_conserves
  State.step_noAir
  State.step_free
  State.free_after_edit
  State.step_entities_sound
  State.not_occupied_iff
  State.Sound.step
  State.Sound.run
  Terrain.initial_sound
  Terrain.play_sound

-- Pacing: frames, ticks and input
#assert_standard_axioms
  Command.not_dig_and_place
  State.runLog_edits
  Session.frameLog_edits
  Session.frame_dig_exact
  Session.frame_place_exact
  Session.frame_pending_quiet
  Session.frame_pending_cleared_of_not_both
  Session.drop_two_commands
  Session.play_place_count
  Session.play_selectIntent
  Session.play_flyIntent
  Session.play_terrain
  Session.play_seed
  State.runLog_state
  Session.frameLog_fst
  Session.tail_commands
  Session.frame_pending_cleared
  Session.debt_lt
  Session.time_not_invented
  Session.time_accounted
  Session.play_state
  Session.play_dig_iff
  Session.play_dig_count
  Session.play_place_iff
  Session.frame_flyIntent
  Session.frame_selectIntent
  Session.play_sound
  Terrain.session_sound
  Terrain.flatWorld_floor
  Terrain.world_floor_get

-- The view: what to load, drop and rebuild
#assert_standard_axioms
  ViewRange.contains_iff_offset
  ViewRange.not_isFar_of_contains
  mem_dirtyChunks
  meshChunk_set_of_not_dirty

-- Progress: things that should happen do
#assert_standard_axioms
  Shape.moveAxis_of_free
  Player.step_rest
  State.edit_dig
  State.edit_place
  State.step_dig
  State.step_place

-- The renderer, against the model of the shim
#assert_standard_axioms
  Gpu.decode_packFaces
  Gpu.decode_meshChunk
  Renderer.Synced.initial
  Renderer.Synced.setMesh
  Renderer.Synced.remesh
  Renderer.Synced.drop
  Renderer.Synced.applyEdit
  Renderer.Synced.applyEdits
  Renderer.Synced.frame
  Renderer.slots_dropFar_of_contains
  Renderer.Synced.dropFar
  Renderer.Synced.reset
  Renderer.Synced.draw
  Renderer.Synced.scene_sound
  Renderer.Synced.scene_complete

-- The game and its picture, through every step the shell can take
#assert_standard_axioms
  Session.edit?_world
  Client.Synced.start
  Client.Synced.apply
  Client.Synced.run
  Client.run_synced
  Client.run_noFault
  Client.Synced.scene_sound
  Client.Synced.scene_complete
  Client.slots_unloadFar_of_loaded

-- Inventory
#assert_standard_axioms
  Stack.count_bounds
  Inventory.count_add
  Inventory.count_take
  Inventory.Lacks.add
  Inventory.Lacks.take

-- Saving and loading
#assert_standard_axioms
  SaveData.decode?_encode
  SaveData.encode_of_decode?
  SaveData.decode?_injective
  World.get_setMany_toList
  SaveData.restore?_snapshot
  SaveData.restore?_decode_encode
  SaveData.restore?_snapshot_run
  Terrain.session_save_load

-- Everything else: every theorem in every module of the project.
#assert_all_standard_axioms LeanMc "LeanMc/Proofs"
