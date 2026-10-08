import LeanMc.Core.World
import LeanMc.Core.Mesh
import LeanMc.Core.Generated
import LeanMc.Proofs.Player
import LeanMc.Core.Game

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

def palette : Array Block := #[.stone, .dirt, .grass, .sand, .log, .leaves, .planks, .cobble]

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

  -- Player physics, in the flat world: grass top at y = 8, pillars where x and z are multiples of 8.
  let flatSolid := (World.new Terrain.flat).solid
  let run (solid : BlockPos → Bool) (p : Player) (n : Nat) (input : Nat → Input) : Player :=
    (List.range n).foldl (fun p i => p.step solid (input i)) p
  let block (n : Int) : Int := n * 65536
  let dropped := run flatSolid { pos := ⟨block 4 + 32768, block 20, block 4 + 32768⟩ } 120 fun _ => {}
  ok := (← check "a dropped player lands exactly on the ground" <|
    dropped.onGround && dropped.pos.y == block 9 && dropped.vel.y == 0) && ok

  let jumpPeak := (List.range 60).foldl (init := (dropped, dropped.pos.y)) fun (p, peak) i =>
    let p := p.step flatSolid { jump := i == 0 }
    (p, max peak p.pos.y)
  let rise := jumpPeak.2 - block 9
  ok := (← check s!"a jump rises about 1.25 blocks (rose {rise} units) and comes back down" <|
    block 1 + 13107 < rise && rise < block 1 + 19661 && jumpPeak.1.onGround
      && jumpPeak.1.pos.y == block 9) && ok

  -- A pillar stands at (8, 9.., 8). Walk into it from x = 4.5.
  let start : Player := { pos := ⟨block 4 + 32768, block 9, block 8 + 32768⟩ }
  let walked := run flatSolid start 200 fun _ => { wishX := Player.walkSpeed }
  ok := (← check "walking into a pillar stops flush against it" <|
    walked.pos.x + Player.halfWidth == block 8 && walked.vel.x == 0) && ok

  let rushed := run flatSolid { start with flying := true } 200 fun _ => { wishX := 65536 }
  ok := (← check "top speed does not carry the player through a one-block pillar" <|
    rushed.pos.x + Player.halfWidth == block 8) && ok

  -- Random input, checked against the collision test every tick.
  let noise (i : Nat) : Nat := (Terrain.mix (i.toUInt64 + 99)).toNat
  let randomInput (i : Nat) : Input :=
    let r := noise (i / 20)
    { wishX := (r % 131073 : Nat) - 65536, wishZ := (r / 131073 % 131073 : Nat) - 65536,
      jump := r / 7 % 3 == 0, descend := r / 11 % 5 == 0, toggleFly := i % 400 == 399 }
  let gsolid := gw.solid
  let fuzz := (List.range 6000).foldl (init := (({ pos := Terrain.spawn seed } : Player), true))
    fun (p, fine) i =>
      let p := p.step gsolid (randomInput i)
      (p, fine && !Player.blocked gsolid p.pos && p.pos.y ≥ 65536)
  let travelled := (fuzz.1.pos.x - 32768).natAbs + (fuzz.1.pos.z - 32768).natAbs
  ok := (← check s!"6000 ticks of random input never enter a block (ended {travelled / 65536} blocks away)" <|
    fuzz.2 && travelled > 65536) && ok

  -- The flat world repeats every 120 blocks in x and z, so a shifted run must match exactly.
  let d : BlockPos := ⟨120 * far, 0, -120 * far⟩
  let here := run flatSolid start 600 randomInput
  let there := run flatSolid (Player.shift start d) 600 randomInput
  ok := (← check "the same inputs give the same motion a long way from the origin" <|
    there.pos == here.pos.shift d && there.vel == here.vel && there.onGround == here.onGround) && ok

  -- Targeting: the exact walk against a brute-force march along the same segment.
  let march (solid : BlockPos → Bool) (o v : Vec3) : Option BlockPos :=
    (List.range 4097).findSome? fun (k : Nat) =>
      let c := (⟨o.x + v.x * k / 4096, o.y + v.y * k / 4096, o.z + v.z * k / 4096⟩ : Vec3).blockPos
      if solid c then some c else none
  let rays : List (Vec3 × Vec3) := (List.range 400).map fun i =>
    let r := noise (i + 5000)
    let part (k : Nat) (span : Nat) : Int := ((r / k % span : Nat) : Int)
    (⟨block 2 + part 1 393216, block 9 + part 7 131072, block 2 + part 13 393216⟩,
     ⟨part 17 655361 - 327680, part 19 655361 - 327680, part 23 655361 - 327680⟩)
  let agree := rays.filter fun (o, v) => (Ray.cast flatSolid o v).map (·.block) == march flatSolid o v
  let hits := rays.filter fun (o, v) => (Ray.cast flatSolid o v).isSome
  ok := (← check s!"targeting agrees with a brute-force march ({agree.length} of {rays.length} rays, \
      {hits.length} of them hits)" <|
    agree.length * 100 ≥ rays.length * 97 && hits.length > 50) && ok

  -- The game rules, in the flat world. The player stands on the grass at (4.5, 9, 4.5).
  let flatWorld := World.new Terrain.flat
  let standing : State := ⟨flatWorld, dropped⟩
  let down : Vec3 := ⟨0, -327680, 0⟩
  let dug := standing.step { look := down, dig := true }
  ok := (← check "digging removes the block being looked at and nothing else" <|
    standing.target down == some ⟨⟨4, 8, 4⟩, some .yp⟩
      && dug.world.get ⟨4, 8, 4⟩ == .air && dug.world.get ⟨4, 7, 4⟩ == .dirt
      && dug.world.get ⟨5, 8, 4⟩ == .grass) && ok

  let fell := dug.run (List.replicate 60 {})
  ok := (← check "the player then falls into the hole" <|
    fell.player.pos.y == block 8 && fell.player.onGround) && ok

  let buried := standing.step { look := down, place := some .cobble }
  ok := (← check "placing where the player stands is refused" <|
    (standing.edit { look := down, place := some .cobble }).isNone
      && buried.world.get ⟨4, 9, 4⟩ == .air) && ok

  let ahead : Vec3 := ⟨196608, -150000, 0⟩
  let placed := standing.step { look := ahead, place := some .cobble }
  let cell := (standing.target ahead).bind fun hit => hit.face.map hit.block.step
  ok := (← check "placing fills the empty cell in front of the targeted face" <|
    match cell with
    | some q => flatWorld.get q == .air && placed.world.get q == .cobble
    | none => false) && ok

  -- Clear a shaft down to bedrock and stand in it.
  let shaft := (List.range 8).foldl (fun w (i : Nat) => w.set ⟨4, 1 + (i : Int), 4⟩ .air) flatWorld
  let atBottom : State := ⟨shaft, { pos := ⟨block 4 + 32768, block 1, block 4 + 32768⟩ }⟩
  ok := (← check "bedrock cannot be dug" <|
    atBottom.target down == some ⟨⟨4, 0, 4⟩, some .yp⟩
      && (atBottom.step { look := down, dig := true }).world.get ⟨4, 0, 4⟩ == .bedrock) && ok

  let high : State := ⟨flatWorld, { pos := ⟨block 4 + 32768, block 20, block 4 + 32768⟩, flying := true }⟩
  ok := (← check "a block out of reach is not targeted, however long the look vector" <|
    (high.target ⟨0, -block 1000, 0⟩).isNone) && ok

  -- Random play in the generated world, checked every tick.
  let randomCommand (i : Nat) : Command :=
    let r := noise (i + 77777)
    let part (k : Nat) : Int := ((r / k % 655361 : Nat) : Int) - 327680
    { move := randomInput i, look := ⟨part 3, part 5 - 150000, part 9⟩,
      dig := r % 4 == 0, place := if r % 4 == 1 then palette[r / 31 % 8]? else none }
  let play := (List.range 5000).foldl (init := (Terrain.initial seed, true, 0))
    fun (s, fine, edits) i =>
      let cmd := randomCommand i
      let edit := s.edit cmd
      let next := s.step cmd
      let feet := next.player.pos.blockPos
      let fine := fine && !Player.blocked next.world.solid next.player.pos
        && next.player.pos.y ≥ 65536 && next.world.get ⟨feet.x, 0, feet.z⟩ == .bedrock
        && (match edit with
            | some (q, b) => next.world.get q == b
            | none => true)
      (next, fine, edits + (if edit.isSome then 1 else 0))
  ok := (← check s!"5000 ticks of random digging, placing and moving stay sound \
      ({play.2.2} blocks changed)" (play.2.1 && play.2.2 > 100)) && ok

  return if ok then 0 else 1
