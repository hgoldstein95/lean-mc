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

/-! ## Newcomers to the generated world -/

/-- The untouched world is solid exactly where its terrain is. -/
theorem world_solid (seed : UInt64) : (world seed).solid = solid seed := by
  funext p
  simp only [World.solid, world_get, solid]

theorem solid_floor (seed : UInt64) (x z : Int) : solid seed ⟨x, 0, z⟩ = true := by
  simp [solid, generate_bedrock, Block.isSolid]

/-- Nothing is generated at a column's drop point, for a body no wider than a block. -/
theorem dropPoint_free (seed : UInt64) {sh : Shape} (hw : sh.halfWidth ≤ 32768) (x z : Int) :
    sh.Free (solid seed) (dropPoint seed x z) := by
  have hpos := sh.halfWidth_ge
  have hh := sh.height_ge
  intro p hp
  obtain ⟨px, py, pz⟩ := p
  simp only [Box.Overlaps, Shape.box, dropPoint] at hp
  have hx : px = x := by omega
  have hz : pz = z := by omega
  subst hx hz
  have hy : height seed px pz + maxTreeHeight < py := by simp only [maxTreeHeight] at hp ⊢; omega
  simp only [solid]
  rw [generate_above_column seed (p := ⟨px, py, pz⟩) hy]
  rfl

/-- **A newcomer is not inside anything.** -/
theorem standing_free (seed : UInt64) {sh : Shape} (hw : sh.halfWidth ≤ 32768) (x z : Int) :
    sh.Free (solid seed) (standing seed sh x z) :=
  Shape.settle_free 16 (dropPoint_free seed hw x z)

/--
**A newcomer stands on the ground.** Settling stops with something solid
directly beneath: the search starts above the tallest tree and the ground is
never more than nine blocks below that.
-/
theorem standing_grounded (seed : UInt64) {sh : Shape} (hw : sh.halfWidth ≤ 32768) (x z : Int) :
    sh.blocked (solid seed) ((standing seed sh x z).add .y (-1)) = true := by
  have hpos := sh.halfWidth_ge
  have hh := sh.height_ge
  refine Shape.settle_grounded 16 (dropPoint_free seed hw x z)
    (by simp only [dropPoint]; omega) ⟨8, by decide, ?_⟩
  refine Box.collides_eq_true_iff.mpr ⟨⟨x, height seed x z, z⟩, ?_, ?_⟩
  · simp only [Box.Overlaps, Shape.box, Vec3.add, dropPoint, maxTreeHeight]
    omega
  · exact generate_surface_isSolid seed x z

/-- A newcomer stands above the floor. -/
theorem standing_above (seed : UInt64) (sh : Shape) (x z : Int) :
    65536 ≤ (standing seed sh x z).y := by
  have hb := height_bounds seed x z
  refine Shape.settle_above_floor (solid_floor seed) 16 ?_ ?_ <;>
    simp only [dropPoint, minHeight, maxTreeHeight] at hb ⊢ <;> omega

/-- A newcomer stands in the middle of the column of blocks it was dropped into. -/
theorem standing_xz (seed : UInt64) (sh : Shape) (x z : Int) :
    (standing seed sh x z).x = x * 65536 + 32768 ∧ (standing seed sh x z).z = z * 65536 + 32768 :=
  sh.settle_xz (solid seed) 16 (dropPoint seed x z)

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

/-- **A new player is not inside anything.** -/
theorem spawn_free (seed : UInt64) : Player.Free (world seed).solid (spawn seed) := by
  rw [world_solid]
  exact standing_free seed (by decide) 0 0

/-- **A new player stands on the ground.** -/
theorem spawn_grounded (seed : UInt64) :
    Player.blocked (world seed).solid ((spawn seed).add .y (-1)) = true := by
  rw [world_solid]
  exact standing_grounded seed (by decide) 0 0

/-! ## The foxes of the generated world -/

/-- A column of chunks starts with at most one fox. -/
theorem creatures_length (seed : UInt64) (cx cz : Int) : (creatures seed cx cz).length ≤ 1 := by
  simp only [creatures]
  split <;> simp

/--
**Every generated fox is sound.** In the untouched world it is clear of
blocks, above the floor, at rest and standing on the ground, and knows it.
-/
theorem creatures_sound (seed : UInt64) (cx cz : Int) :
    ∀ e ∈ creatures seed cx cz, e.Sound (world seed).solid ∧ e.onGround = true := by
  intro e he
  rw [world_solid]
  simp only [creatures] at he
  split at he
  · simp only [List.mem_singleton] at he
    subst he
    exact ⟨Entity.resting_sound _ (standing_free seed (by decide) _ _) (standing_above ..),
      (Entity.resting_onGround ..).trans (standing_grounded seed (by decide) _ _)⟩
  · cases he

/-- **A column's fox stands in that column.** -/
theorem creatures_column (seed : UInt64) (cx cz : Int) :
    ∀ e ∈ creatures seed cx cz, e.chunk.x = cx ∧ e.chunk.z = cz := by
  intro e he
  simp only [creatures] at he
  split at he
  · simp only [List.mem_singleton] at he
    subst he
    have hxz := standing_xz seed Entity.shape
      (16 * cx + (((hash (seed + 5) cx cz >>> 8).toNat % 16 : Nat) : Int))
      (16 * cz + (((hash (seed + 5) cx cz >>> 16).toNat % 16 : Nat) : Int))
    simp only [Entity.chunk, Entity.resting_pos, Vec3.blockPos, BlockPos.chunkPos, hxz]
    omega
  · cases he

/-- **No generated fox is left out.** In the untouched world every one passes the check made of it. -/
theorem creatures_filter (seed : UInt64) (cx cz : Int) :
    ((world seed).creatures cx cz).filter (fun e => decide (e.Sound (world seed).solid))
      = creatures seed cx cz := by
  show (creatures seed cx cz).filter _ = _
  exact List.filter_eq_self.mpr fun e he => decide_eq_true (creatures_sound seed cx cz e he).1

/-! ## The game as a whole -/

/-- A new game starts in a sound state. -/
theorem initial_sound (seed : UInt64) : (initial seed).Sound where
  free := spawn_free seed
  floor x z := by simp [initial, generate_bedrock]
  items := Inventory.noAir_empty
  bedrock := Inventory.lacks_empty _
  speed := by
    show Body.Bounded ⟨0, 0, 0⟩
    decide
  grounded := by
    show (newcomer seed).onGround
      = Player.blocked (world seed).solid ((newcomer seed).pos.add .y (-1))
    rw [world_solid]
    rfl
  above := standing_above seed Player.shape 0 0
  entities := by
    obtain ⟨new, heq, hnew⟩ :=
      State.populate_entities (world seed) (newcomer seed).chunk [] {}
    intro e he
    simp only [initial, heq, List.nil_append] at he
    exact hnew e he

/-- A new game starts with the creatures of every loaded column made. -/
theorem initial_populated (seed : UInt64) : (initial seed).Populated := by
  intro c hc
  simp only [initial, State.centre] at hc ⊢
  exact (State.populate_populated ..).2 c hc

/-- A new game starts with the player on the ground, and knowing it. -/
theorem initial_onGround (seed : UInt64) : (initial seed).player.onGround = true :=
  standing_grounded seed (by decide) 0 0

/--
**The game never goes wrong.** Whatever the seed and whatever commands are
played, for however long: the player is never inside a solid block, the
bedrock floor is never broken, and the player never falls through it.
-/
theorem play_sound (seed : UInt64) (cmds : List Command) : ((initial seed).run cmds).Sound :=
  (initial_sound seed).run cmds

/--
**Whatever is loaded has been populated.** Whatever commands are played, every
column of chunks loaded around the player has had its creatures made.
-/
theorem play_populated (seed : UInt64) (cmds : List Command) :
    ((initial seed).run cmds).Populated :=
  (initial_populated seed).run cmds

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
  have hs : w'.solid = Body.shiftSolid w.solid d := by
    funext q
    have hq : (⟨q.x - d.x + d.x, q.y - d.y + d.y, q.z - d.z + d.z⟩ : BlockPos) = q := by
      ext <;> simp
    simp only [World.solid, Body.shiftSolid, ← h, hq]
  rw [hs, Player.step_shift]

end LeanMc.World
