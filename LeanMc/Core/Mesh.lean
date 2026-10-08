import LeanMc.Core.Chunk

/-!
# Meshing

Turns the blocks of a chunk into the triangles that draw it. A block face is
emitted exactly when the block is visible and its neighbour on that side does
not hide it.

The mesher reads blocks through a function rather than from a chunk, so the
same definition serves both as the specification (reading the world) and as
the implementation (reading the chunk cache).

Vertices are packed as 8 bytes each, all integers; `ffi/shim.c` documents the
layout and expands them for the GPU.
-/

namespace LeanMc

namespace Block

/-- Atlas tile shown on each face of a block. Tiles are numbered row by row. -/
def tile : Block → Dir → Nat
  | air, _ => 0
  | bedrock, _ => 0
  | stone, _ => 1
  | dirt, _ => 2
  | grass, .yp => 3
  | grass, .yn => 2
  | grass, _ => 4
  | sand, _ => 5
  | log, .yp => 7
  | log, .yn => 7
  | log, _ => 6
  | leaves, _ => 8
  | planks, _ => 9
  | cobble, _ => 10

end Block

namespace Dir

/-- Brightness of a face, standing in for lighting. -/
def shade : Dir → UInt8
  | xp => 200 | xn => 200 | yp => 255 | yn => 120 | zp => 170 | zn => 170

/--
The four corners of a unit block's face, as offsets from the block's minimum
corner. Seen from outside they run counter-clockwise from the bottom right:
bottom right, top right, top left, bottom left.
-/
def corner : Dir → Fin 4 → Nat × Nat × Nat
  | xp, 0 => (1, 0, 0) | xp, 1 => (1, 1, 0) | xp, 2 => (1, 1, 1) | xp, 3 => (1, 0, 1)
  | xn, 0 => (0, 0, 1) | xn, 1 => (0, 1, 1) | xn, 2 => (0, 1, 0) | xn, 3 => (0, 0, 0)
  | yp, 0 => (0, 1, 0) | yp, 1 => (0, 1, 1) | yp, 2 => (1, 1, 1) | yp, 3 => (1, 1, 0)
  | yn, 0 => (0, 0, 1) | yn, 1 => (0, 0, 0) | yn, 2 => (1, 0, 0) | yn, 3 => (1, 0, 1)
  | zp, 0 => (1, 0, 1) | zp, 1 => (1, 1, 1) | zp, 2 => (0, 1, 1) | zp, 3 => (0, 0, 1)
  | zn, 0 => (0, 0, 0) | zn, 1 => (0, 1, 0) | zn, 2 => (1, 1, 0) | zn, 3 => (1, 0, 0)

end Dir

/-- Texture offset of each face corner within its tile, matching `Dir.corner`. -/
def cornerUV : Fin 4 → Nat × Nat
  | 0 => (1, 1) | 1 => (1, 0) | 2 => (0, 0) | 3 => (0, 1)

/-- One visible face of a block in a chunk. -/
structure Face where
  pos : LocalPos
  dir : Dir
  block : Block
  deriving DecidableEq, Repr

/-- Whether the face of the block at `p` on side `d` should be drawn. -/
def faceVisible (blockAt : BlockPos → Block) (p : BlockPos) (d : Dir) : Bool :=
  (blockAt p).isVisible && !(blockAt (p.step d)).isOpaque

/-- The faces to draw for the block at `l` in chunk `c`. -/
def blockFaces (blockAt : BlockPos → Block) (c : ChunkPos) (l : LocalPos) : List Face :=
  let p := c.blockAt l
  Dir.all.filterMap fun d =>
    if faceVisible blockAt p d then some ⟨l, d, blockAt p⟩ else none

/-- The faces to draw for chunk `c`. -/
def chunkFaces (blockAt : BlockPos → Block) (c : ChunkPos) : List Face :=
  LocalPos.all.flatMap (blockFaces blockAt c)

namespace Face

/-- Number of bytes in one packed vertex. -/
def vertexBytes : Nat := 8

/-- Corners used by the two triangles of a face. -/
def triangleCorners : List (Fin 4) := [0, 1, 2, 0, 2, 3]

/-- Append the packed vertex for one corner of a face. -/
def pushVertex (f : Face) (out : ByteArray) (i : Fin 4) : ByteArray :=
  let (cx, cy, cz) := f.dir.corner i
  let (cu, cv) := cornerUV i
  let tile := f.block.tile f.dir
  out
    |>.push (f.pos.x.val + cx).toUInt8
    |>.push (f.pos.y.val + cy).toUInt8
    |>.push (f.pos.z.val + cz).toUInt8
    |>.push (tile % 16 + cu).toUInt8
    |>.push (tile / 16 + cv).toUInt8
    |>.push f.dir.shade
    |>.push f.dir.toNat.toUInt8
    |>.push 0

/-- Append the six packed vertices of a face. -/
def push (out : ByteArray) (f : Face) : ByteArray :=
  triangleCorners.foldl f.pushVertex out

end Face

/-- Pack faces into the vertex buffer handed to the renderer. -/
def packFaces (faces : List Face) : ByteArray :=
  faces.foldl Face.push ByteArray.empty

/-- The vertex buffer for chunk `c`. -/
def meshChunk (blockAt : BlockPos → Block) (c : ChunkPos) : ByteArray :=
  packFaces (chunkFaces blockAt c)

end LeanMc
