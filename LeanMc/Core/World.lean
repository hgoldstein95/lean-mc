import Std.Data.HashMap
import LeanMc.Proofs.Chunk

/-!
# The world

The world is a terrain function with a finite overlay of edits. Reading a
block consults the overlay first and falls back to the terrain, so the world
is defined at every position and never needs to be "loaded".

Chunks are a derived view: `World.chunk` materialises one, and `ChunkCache`
keeps materialised chunks around for fast repeated reads. The cache is an
optimisation only; `LeanMc.Proofs.World` shows it always agrees with the world.
-/

namespace LeanMc

structure World where
  /-- What the world contains before anyone changes it. -/
  terrain : BlockPos → Block
  /-- A way to produce a whole chunk of terrain at once, typically faster than block by block. -/
  terrainChunk : ChunkPos → Chunk
  /-- The chunk generator produces exactly the terrain. -/
  terrainChunk_get : ∀ c l, (terrainChunk c).get l = terrain (c.blockAt l)
  /-- Blocks that have been changed, by position. -/
  edits : Std.HashMap BlockPos Block := {}

namespace World

/-- A world nobody has changed yet, generating its chunks block by block. -/
def new (terrain : BlockPos → Block) : World where
  terrain
  terrainChunk c := Chunk.ofFn fun l => terrain (c.blockAt l)
  terrainChunk_get _ _ := Chunk.get_ofFn ..

/-- A world nobody has changed yet, with a chunk generator proved to match its terrain. -/
def newWithChunks (terrain : BlockPos → Block) (terrainChunk : ChunkPos → Chunk)
    (h : ∀ c l, (terrainChunk c).get l = terrain (c.blockAt l)) : World where
  terrain
  terrainChunk
  terrainChunk_get := h

def get (w : World) (p : BlockPos) : Block :=
  match w.edits[p]? with
  | some b => b
  | none => w.terrain p

/-- Whether the block at `p` stops movement. -/
def solid (w : World) (p : BlockPos) : Bool :=
  (w.get p).isSolid

def set (w : World) (p : BlockPos) (b : Block) : World :=
  { w with edits := w.edits.insert p b }

/-- Apply a list of edits in order. -/
def setMany (w : World) (edits : List (BlockPos × Block)) : World :=
  edits.foldl (fun w e => w.set e.1 e.2) w

/-- The blocks of chunk `c`, materialised: its terrain with the edits laid over it. -/
def chunk (w : World) (c : ChunkPos) : Chunk :=
  let base := w.terrainChunk c
  if w.edits.isEmpty then base
  else Chunk.ofFn fun l =>
    match w.edits[c.blockAt l]? with
    | some b => b
    | none => base.get l

end World

/-- Materialised chunks, kept so that reads do not re-evaluate the terrain. -/
structure ChunkCache where
  chunks : Std.HashMap ChunkPos Chunk := {}

namespace ChunkCache

/-- Read a block through the cache, falling back to the world for chunks not held. -/
def blockAt (cache : ChunkCache) (w : World) (p : BlockPos) : Block :=
  match cache.chunks[p.chunkPos]? with
  | some chunk => chunk.get p.localPos
  | none => w.get p

/-- Make sure chunk `c` is held. -/
def load (cache : ChunkCache) (w : World) (c : ChunkPos) : ChunkCache :=
  if cache.chunks.contains c then cache else ⟨cache.chunks.insert c (w.chunk c)⟩

def unload (cache : ChunkCache) (c : ChunkPos) : ChunkCache :=
  ⟨cache.chunks.erase c⟩

/-- Mirror a `World.set` in the cache, touching only the chunk that holds `p`. -/
def setBlock (cache : ChunkCache) (p : BlockPos) (b : Block) : ChunkCache :=
  ⟨cache.chunks.modify p.chunkPos (·.set p.localPos b)⟩

end ChunkCache

end LeanMc
