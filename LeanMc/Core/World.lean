import Std.Data.HashMap
import LeanMc.Core.Chunk

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
  /-- Blocks that have been changed, by position. -/
  edits : Std.HashMap BlockPos Block := {}

namespace World

/-- A world nobody has changed yet. -/
def new (terrain : BlockPos → Block) : World :=
  { terrain }

def get (w : World) (p : BlockPos) : Block :=
  match w.edits[p]? with
  | some b => b
  | none => w.terrain p

def set (w : World) (p : BlockPos) (b : Block) : World :=
  { w with edits := w.edits.insert p b }

/-- Apply a list of edits in order. -/
def setMany (w : World) (edits : List (BlockPos × Block)) : World :=
  edits.foldl (fun w e => w.set e.1 e.2) w

/-- The blocks of chunk `c`, materialised. -/
def chunk (w : World) (c : ChunkPos) : Chunk :=
  Chunk.ofFn fun l => w.get (c.blockAt l)

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
