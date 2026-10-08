import Lean
import LeanMc.Proofs.Pos
import LeanMc.Proofs.Chunk
import LeanMc.Proofs.World

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
