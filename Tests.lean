import LeanMc.Core.World
import LeanMc.Core.Mesh
import LeanMc.Core.Generated

/-!
Executable checks on the pure core, run with `lake test`. They complement the
proofs by exercising the compiled code on concrete worlds.
-/

open LeanMc

def check (name : String) (ok : Bool) : IO Bool := do
  IO.println s!"{if ok then "ok  " else "FAIL"}  {name}"
  return ok

def edits : List (BlockPos × Block) :=
  [(⟨3, 8, 5⟩, .air), (⟨3, 7, 5⟩, .air), (⟨15, 8, 6⟩, .air), (⟨-1, 8, -1⟩, .air),
   (⟨0, 9, 16⟩, .planks), (⟨-17, 12, 31⟩, .leaves), (⟨15, 8, 6⟩, .cobble), (⟨15, 8, 6⟩, .air)]

def range (lo hi : Int) : List Int :=
  (List.range (hi - lo + 1).toNat).map fun (i : Nat) => lo + Int.ofNat i

def chunks : List ChunkPos :=
  (range (-2) 2).flatMap fun x => (range (-1) 1).flatMap fun y => (range (-2) 2).map fun z =>
    ⟨x, y, z⟩

/-- Height of the flat world's pillar at a pillar position. -/
def pillarHeight (x z : Int) : Nat :=
  (1 + (x / 8 + z / 8) % 3).toNat

def main : IO UInt32 := do
  let w0 := World.new Terrain.flat
  let mut cache : ChunkCache := {}
  for c in chunks do
    cache := cache.load w0 c
  let mut w := w0
  for (p, b) in edits do
    w := w.set p b
    cache := cache.setBlock p b

  let mut ok := true

  ok := (← check "cached reads match the world after edits" <|
    chunks.all fun c => LocalPos.all.all fun l =>
      cache.blockAt w (c.blockAt l) == w.get (c.blockAt l)) && ok

  let inner := chunks.filter fun c => c.x.natAbs ≤ 1 && c.y == 0 && c.z.natAbs ≤ 1
  ok := (← check "meshes built through the cache match meshes built from the world" <|
    inner.all fun c => meshChunk (cache.blockAt w) c == meshChunk w.get c) && ok

  ok := (← check "a mesh is 48 bytes per face" <|
    inner.all fun c => (meshChunk w.get c).size == 48 * (chunkFaces w.get c).length) && ok

  -- Chunk (2, 0, 2) is untouched flat ground: bedrock underside, grass, four pillars.
  let pillars := [(32, 32), (32, 40), (40, 32), (40, 40)]
  let expected := 256 + (256 - 4) + (pillars.map fun (x, z) => 4 * pillarHeight x z + 1).sum
  ok := (← check s!"flat ground has the expected {expected} faces" <|
    (chunkFaces w0.get ⟨2, 0, 2⟩).length == expected) && ok

  -- Removing a block on a chunk's edge exposes a face of the next chunk.
  let w1 := w0.set ⟨15, 8, 6⟩ .air
  ok := (← check "an edit at a chunk edge changes the neighbouring chunk's mesh" <|
    meshChunk w1.get ⟨1, 0, 0⟩ != meshChunk w0.get ⟨1, 0, 0⟩
      && (chunkFaces w1.get ⟨1, 0, 0⟩).length == (chunkFaces w0.get ⟨1, 0, 0⟩).length + 1) && ok

  ok := (← check "an edit leaves non-adjacent chunks' meshes alone" <|
    meshChunk w1.get ⟨2, 0, 0⟩ == meshChunk w0.get ⟨2, 0, 0⟩
      && meshChunk w1.get ⟨0, 0, 1⟩ == meshChunk w0.get ⟨0, 0, 1⟩) && ok

  ok := (← check "positions split and rejoin on both sides of the origin" <|
    [(-33 : Int), -17, -16, -1, 0, 1, 15, 16, 1000000000000000000000].all fun n =>
      let p : BlockPos := ⟨n, -n, n + 7⟩
      p.chunkPos.blockAt p.localPos == p) && ok

  -- Generated terrain
  let seed : UInt64 := 2026
  let far : Int := 1000000000000000000000
  let sampleChunks : List ChunkPos :=
    [⟨0, 3, 0⟩, ⟨-1, 2, 5⟩, ⟨7, 4, -3⟩, ⟨0, 0, 0⟩, ⟨0, 9, 0⟩, ⟨far, 3, -far⟩, ⟨-far - 1, 2, far⟩]
  ok := (← check "the chunk generator matches the pointwise terrain, near and far" <|
    sampleChunks.all fun c => LocalPos.all.all fun l =>
      (Terrain.generateChunk seed c).get l == Terrain.generate seed (c.blockAt l)) && ok

  let columns : List (Int × Int) :=
    (range (-40) 40).flatMap fun i => [(i * 37, i * 91 - 5), (far + i, i - far), (-far * far + i, i)]
  ok := (← check "ground height stays within its bounds, near and far" <|
    columns.all fun (x, z) =>
      let h := Terrain.height seed x z
      Terrain.minHeight ≤ h && h ≤ Terrain.maxHeight) && ok

  let heights := columns.map fun (x, z) => Terrain.height seed x z
  ok := (← check "the land is not flat" <|
    heights.any (· != heights.head!) && heights.any (· ≥ Terrain.sandLevel)
      && heights.any (· < Terrain.sandLevel)) && ok

  ok := (← check "different seeds give different land" <|
    columns.any fun (x, z) => Terrain.height seed x z != Terrain.height (seed + 1) x z) && ok

  -- The chunk holding the surface at the origin, so that it has faces to check.
  let gw := Terrain.world seed
  let surface : ChunkPos := ⟨0, Terrain.height seed 8 8 / 16, 0⟩
  let mut gcache : ChunkCache := {}
  for c in [surface, surface.step .xp, surface.step .yn] do
    gcache := gcache.load gw c
  let faces := chunkFaces gw.get surface
  IO.println s!"      (surface chunk {surface.x} {surface.y} {surface.z} has {faces.length} faces)"
  ok := (← check "the surface chunk has faces" (faces.length > 0)) && ok

  ok := (← check "generated terrain meshes the same through the cache as from the world" <|
    meshChunk (gcache.blockAt gw) surface == meshChunk gw.get surface) && ok

  ok := (← check "no face is emitted twice" (faces.eraseDups.length == faces.length)) && ok

  return if ok then 0 else 1
