import LeanMc.Core.Generated
import LeanMc.Proofs.World
import LeanMc.Proofs.Mesh
import LeanMc.Proofs.Player
import LeanMc.Proofs.Game

/-!
# Theorems about the generated world

These tie the pieces together for the world the game actually runs: its chunks
are a function of the seed and position alone, and what is drawn is exactly
what the terrain and the edits say should be visible.
-/

namespace LeanMc.Terrain

@[simp] theorem world_get (seed : UInt64) (p : BlockPos) : (world seed).get p = generate seed p := by
  simp [world, World.newWithChunks, World.get]

/--
**Generation does not depend on order.** A chunk of the untouched world holds
exactly the terrain function's blocks, whichever chunks were generated before
it and however often it has been generated.
-/
theorem world_chunk_get (seed : UInt64) (c : ChunkPos) (l : LocalPos) :
    ((world seed).chunk c).get l = generate seed (c.blockAt l) := by
  rw [World.get_chunk, world_get]

/-- After any edits, a position nobody wrote still holds its generated block. -/
theorem world_setMany_get (seed : UInt64) (edits : List (BlockPos × Block)) (p : BlockPos)
    (h : ∀ e ∈ edits, e.1 ≠ p) : ((world seed).setMany edits).get p = generate seed p := by
  rw [World.get_setMany_of_not_mem _ _ _ h, world_get]

/--
**What is drawn is what is there.** Through any valid chunk cache and after any
edits, a face is in a chunk's mesh exactly when the world's block there is
visible and the world's block beside it is not opaque.
-/
theorem mem_chunkFaces_cache {cache : ChunkCache} {w : World} (h : cache.Valid w) {c : ChunkPos}
    {f : Face} :
    f ∈ chunkFaces (cache.blockAt w) c ↔
      faceVisible w.get (c.blockAt f.pos) f.dir = true ∧ f.block = w.get (c.blockAt f.pos) := by
  have : cache.blockAt w = w.get := funext h.blockAt_eq
  rw [this, mem_chunkFaces]

/-! ## The player in the generated world -/

theorem spawnStart_free (seed : UInt64) : Player.Free (world seed).solid (spawnStart seed) := by
  intro p hp
  obtain ⟨x, y, z⟩ := p
  simp only [Box.Overlaps, Player.box, spawnStart, Player.halfWidth, Player.height] at hp
  have hx : x = 0 := by omega
  have hz : z = 0 := by omega
  subst hx hz
  have hy : height seed 0 0 + maxTreeHeight < y := by simp only [maxTreeHeight] at hp ⊢; omega
  simp only [World.solid, world_get]
  rw [generate_above_column seed (p := ⟨0, y, 0⟩) hy]
  rfl

/-- **A new player is not inside anything.** -/
theorem spawn_free (seed : UInt64) : Player.Free (world seed).solid (spawn seed) :=
  Player.settle_free 16 (spawnStart_free seed)

/-- The generated world has a solid floor at height zero. -/
theorem world_floor (seed : UInt64) (x z : Int) : (world seed).solid ⟨x, 0, z⟩ = true := by
  simp [World.solid, generate_bedrock, Block.isSolid]

/--
**Nobody falls out of the world.** In the untouched generated world, a player
whose feet are above bedrock keeps them above bedrock.
-/
theorem step_above_bedrock (seed : UInt64) (input : Input) {p : Player} (h : 65536 ≤ p.pos.y) :
    65536 ≤ (Player.step (world seed).solid input p).pos.y :=
  Player.step_above_floor (world_floor seed) input h

/-! ## The game as a whole -/

/-- A new game starts in a sound state. -/
theorem initial_sound (seed : UInt64) : (initial seed).Sound where
  free := spawn_free seed
  floor x z := by simp [initial, generate_bedrock]
  above := by
    have hb := height_bounds seed 0 0
    refine Player.settle_above_floor (world_floor seed) 16 ?_ ?_ <;>
      simp only [spawnStart, minHeight, maxTreeHeight] at hb ⊢ <;> omega

/--
**The game never goes wrong.** Whatever the seed and whatever commands are
played, for however long: the player is never inside a solid block, the
bedrock floor is never broken, and the player never falls through it.
-/
theorem play_sound (seed : UInt64) (cmds : List Command) : ((initial seed).run cmds).Sound :=
  (initial_sound seed).run cmds

end LeanMc.Terrain

namespace LeanMc.World

/--
**Physics is the same everywhere, stated for worlds.** If one world is another
moved by `d` blocks, then a tick in it is the tick in the other, moved by `d`.
-/
theorem step_translate {w w' : World} (d : BlockPos)
    (h : ∀ p : BlockPos, w'.get ⟨p.x + d.x, p.y + d.y, p.z + d.z⟩ = w.get p)
    (input : Input) (p : Player) :
    Player.step w'.solid input (p.shift d) = (Player.step w.solid input p).shift d := by
  have hs : w'.solid = Player.shiftSolid w.solid d := by
    funext q
    have hq : (⟨q.x - d.x + d.x, q.y - d.y + d.y, q.z - d.z + d.z⟩ : BlockPos) = q := by
      ext <;> simp
    simp only [World.solid, Player.shiftSolid, ← h, hq]
  rw [hs, Player.step_shift]

end LeanMc.World
