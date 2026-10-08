import LeanMc.Core.View

/-!
# The renderer: a model of the graphics side, and the plan that drives it

The native shim keeps a table of uploaded meshes and draws them on request.
This module does two things with that.

`Gpu` is a model of the shim: what a sequence of commands leaves in its mesh
table and what ends up in the scene. It is a description of foreign code, so it
is not proved; tests compare it against the real shim.

`Renderer` is the planner: pure functions that decide which commands to send.
The shell sends them and decides nothing itself. `LeanMc.Proofs.Render` shows
that, against the model, the planner never misuses the shim and that what it
draws is exactly the world's mesh for each loaded chunk.

The planner chooses mesh slots itself, so the shim has no allocation logic.
-/

namespace LeanMc

/-- One instruction to the graphics side. -/
inductive GpuCmd where
  /-- Put a mesh in a slot, replacing whatever was there. -/
  | upload (slot : Nat) (vertices : ByteArray)
  /-- Empty a slot. -/
  | unload (slot : Nat)
  /-- Start a frame's scene with nothing drawn. -/
  | beginScene
  /-- Draw a slot's mesh, moved by `offset` fixed-point units from the eye. -/
  | draw (slot : Nat) (offset : Vec3)

/--
What the shim makes of one packed vertex: its position in whole blocks, its
texture coordinate in sixteenths of the atlas, its brightness, and which of
the six directions its face points in.
-/
structure GpuVertex where
  x : Nat
  y : Nat
  z : Nat
  u : Nat
  v : Nat
  shade : Nat
  normal : Nat
  deriving DecidableEq, Repr

/-- A model of the shim's mesh table and of the scene drawn so far this frame. -/
structure Gpu where
  meshes : Std.HashMap Nat ByteArray := {}
  /-- Draws made since the scene began: which slot, and where. -/
  scene : List (Nat × Vec3) := []
  /-- Whether any command so far was a misuse, such as drawing an empty slot. -/
  fault : Bool := false

namespace Gpu

/-- Number of mesh slots. Slot `0` is never used, so it can mean "no mesh". -/
def capacity : Nat := 16384

/-- Bytes in one triangle: three vertices of eight bytes. -/
def triangleBytes : Nat := 24

/-- What one command does. A misuse changes nothing but is recorded as a fault. -/
def exec (g : Gpu) : GpuCmd → Gpu
  | .upload slot vertices =>
    if slot = 0 ∨ capacity ≤ slot ∨ vertices.size = 0 ∨ vertices.size % triangleBytes ≠ 0 then
      { g with fault := true }
    else { g with meshes := g.meshes.insert slot vertices }
  | .unload slot =>
    if g.meshes.contains slot then { g with meshes := g.meshes.erase slot }
    else { g with fault := true }
  | .beginScene => { g with scene := [] }
  | .draw slot offset =>
    if g.meshes.contains slot then { g with scene := g.scene ++ [(slot, offset)] }
    else { g with fault := true }

def run (g : Gpu) (cmds : List GpuCmd) : Gpu :=
  cmds.foldl exec g

/-- How the shim reads packed vertices, eight bytes at a time; a model of `lmc_decode_vertex`. -/
def decodeList : List UInt8 → List GpuVertex
  | x :: y :: z :: u :: v :: shade :: normal :: _ :: rest =>
    { x := x.toNat, y := y.toNat, z := z.toNat, u := u.toNat, v := v.toNat, shade := shade.toNat
      normal := if normal.toNat < 6 then normal.toNat else 0 } :: decodeList rest
  | _ => []

/-- The vertices the shim sees in a packed mesh. -/
def decode (vertices : ByteArray) : List GpuVertex :=
  decodeList vertices.data.toList

end Gpu

/-- What the planner remembers between frames. -/
structure Renderer where
  cache : ChunkCache := {}
  /-- The slot holding each meshed chunk's mesh. Slot `0` means the chunk has nothing to draw. -/
  slots : Std.HashMap ChunkPos Nat := {}
  /-- Slots that were used and have been emptied, ready for reuse. -/
  free : List Nat := []
  /-- The lowest slot never yet used. -/
  next : Nat := 1

namespace Renderer

/-- Take a slot: a recycled one if there is one, else a fresh one, if any are left. -/
def alloc (r : Renderer) : Option (Nat × Renderer) :=
  match r.free with
  | slot :: rest => some (slot, { r with free := rest })
  | [] =>
    if r.next < Gpu.capacity then some (r.next, { r with next := r.next + 1 }) else none

/-- A chunk cache with `c` and its six neighbours loaded, as meshing `c` needs. -/
def loadAround (cache : ChunkCache) (w : World) (c : ChunkPos) : ChunkCache :=
  Dir.all.foldl (fun cache d => cache.load w (c.step d)) (cache.load w c)

/--
Record that chunk `c`'s mesh is now `vertices`, and say what to send. An empty
mesh needs no slot; a non-empty one keeps the chunk's slot or takes a new one.
If no slot can be had, the chunk goes back to being unmeshed, to be tried again.
-/
def setMesh (r : Renderer) (c : ChunkPos) (vertices : ByteArray) : Renderer × List GpuCmd :=
  let slot := r.slots[c]?.getD 0
  if slot ≠ 0 then
    if vertices.size = 0 then
      ({ r with slots := r.slots.insert c 0, free := slot :: r.free }, [.unload slot])
    else (r, [.upload slot vertices])
  else if vertices.size = 0 then ({ r with slots := r.slots.insert c 0 }, [])
  else
    match r.alloc with
    | some (slot, r) => ({ r with slots := r.slots.insert c slot }, [.upload slot vertices])
    | none => ({ r with slots := r.slots.erase c }, [])

/-- Build chunk `c`'s mesh from the world and bring the graphics side up to date with it. -/
def remesh (r : Renderer) (w : World) (c : ChunkPos) : Renderer × List GpuCmd :=
  let cache := loadAround r.cache w c
  setMesh { r with cache } c (meshChunk (cache.blockAt w) c)

/-- Forget chunk `c`'s mesh, emptying its slot. -/
def drop (r : Renderer) (c : ChunkPos) : Renderer × List GpuCmd :=
  let slot := r.slots[c]?.getD 0
  if slot ≠ 0 then
    ({ r with slots := r.slots.erase c, free := slot :: r.free }, [.unload slot])
  else ({ r with slots := r.slots.erase c }, [])

/-- Apply a planning step to each chunk in turn, collecting the commands. -/
def forEach (step : Renderer → ChunkPos → Renderer × List GpuCmd) (r : Renderer)
    (chunks : List ChunkPos) : Renderer × List GpuCmd :=
  chunks.foldl (fun acc c => ((step acc.1 c).1, acc.2 ++ (step acc.1 c).2)) (r, [])

/--
Follow a block change the world has already had: update the cache and rebuild
every meshed chunk the change can affect.
-/
def applyEdit (r : Renderer) (w : World) (p : BlockPos) (b : Block) : Renderer × List GpuCmd :=
  forEach (·.remesh w) { r with cache := r.cache.setBlock p b }
    ((dirtyChunks p).filter r.slots.contains)

/-- Drop the meshes of chunks far from `centre`, and the cached chunks further out still. -/
def dropFar (r : Renderer) (view : ViewRange) (centre : ChunkPos) : Renderer × List GpuCmd :=
  let dropped := forEach drop r ((r.slots.toList.map (·.1)).filter (view.isFar centre · 1))
  let stale := (dropped.1.cache.chunks.toList.map (·.1)).filter (view.isFar centre · 2)
  ({ dropped.1 with cache := stale.foldl ChunkCache.unload dropped.1.cache }, dropped.2)

/-- Forget everything: empty every slot and the cache, as when a different world is loaded. -/
def reset (r : Renderer) : Renderer × List GpuCmd :=
  let dropped := forEach drop r (r.slots.toList.map (·.1))
  ({ dropped.1 with cache := {} }, dropped.2)

/-- Where chunk `c`'s corner is, measured from the eye, in fixed-point units. -/
def chunkOffset (c : ChunkPos) (eye : Vec3) : Vec3 :=
  ⟨16 * c.x * 65536 - eye.x, 16 * c.y * 65536 - eye.y, 16 * c.z * 65536 - eye.z⟩

/-- The commands that draw every meshed chunk as seen from `eye`. -/
def drawCmds (r : Renderer) (eye : Vec3) : List GpuCmd :=
  .beginScene :: r.slots.toList.filterMap fun (c, slot) =>
    if slot = 0 then none else some (.draw slot (chunkOffset c eye))

end Renderer

end LeanMc
