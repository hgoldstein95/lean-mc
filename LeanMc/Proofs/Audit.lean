import Lean
import LeanMc.Proofs.Pos
import LeanMc.Proofs.Chunk
import LeanMc.Proofs.World
import LeanMc.Proofs.Terrain
import LeanMc.Proofs.Mesh
import LeanMc.Proofs.Player
import LeanMc.Proofs.Ray
import LeanMc.Proofs.Game
import LeanMc.Proofs.Generated

/-!
# Axiom audit

The headline theorems, checked to rest on nothing but Lean's three standard
axioms. In particular this rules out `sorry` and `native_decide`. Building this
module is the check: a violation is a build error.
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

-- Player physics
#assert_standard_axioms
  Box.collides_eq_false_iff
  Player.free_between
  Player.SafeStep.free_between
  Player.step_reach
  Player.step_free
  Player.step_onGround
  Player.step_above_floor
  Player.step_shift
  Player.settle_free
  World.step_translate
  Terrain.generate_above_column
  Terrain.spawn_free
  Terrain.step_above_bedrock

-- Targeting
#assert_standard_axioms
  Ray.cast_solid
  Ray.cast_face_clear
  Ray.cast_walk
  Ray.cast_within

-- The game
#assert_standard_axioms
  State.edit_cases
  State.edit_near
  State.step_changes_at_most_one
  State.step_solid_unchanged_or_air
  State.step_bedrock
  State.step_free
  State.Sound.step
  State.Sound.run
  Terrain.initial_sound
  Terrain.play_sound
