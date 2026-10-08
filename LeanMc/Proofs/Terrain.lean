import LeanMc.Core.Terrain
import LeanMc.Proofs.Chunk

/-!
# Terrain theorems

* The height of the ground is within fixed bounds at every coordinate, however
  large: the noise is a convex combination of bounded values, and nothing can
  overflow.
* The chunk generator, which shares work across a chunk, produces exactly the
  pointwise terrain. So the world does not depend on the order, grouping or
  number of times its chunks are generated.
* There is bedrock at height zero, solid ground up to the surface, and air
  above the tallest possible tree.
-/

namespace LeanMc.Terrain

/-! ## Noise bounds -/

theorem lattice_bounds (seed : UInt64) (x z : Int) :
    0 ≤ lattice seed x z ∧ lattice seed x z ≤ 255 := by
  unfold lattice
  omega

/-- Interpolating between two values in a range stays in that range. -/
theorem lerp_bounds {a b t s lo hi : Int} (hs : 0 < s) (ht : 0 ≤ t) (hts : t ≤ s)
    (ha : lo ≤ a ∧ a ≤ hi) (hb : lo ≤ b ∧ b ≤ hi) :
    lo ≤ lerp a b t s ∧ lerp a b t s ≤ hi := by
  have hst : 0 ≤ s - t := by omega
  have h1 : lo * (s - t) ≤ a * (s - t) := Int.mul_le_mul_of_nonneg_right ha.1 hst
  have h2 : a * (s - t) ≤ hi * (s - t) := Int.mul_le_mul_of_nonneg_right ha.2 hst
  have h3 : lo * t ≤ b * t := Int.mul_le_mul_of_nonneg_right hb.1 ht
  have h4 : b * t ≤ hi * t := Int.mul_le_mul_of_nonneg_right hb.2 ht
  have e1 : lo * (s - t) + lo * t = lo * s := by rw [← Int.mul_add]; congr 1; omega
  have e2 : hi * (s - t) + hi * t = hi * s := by rw [← Int.mul_add]; congr 1; omega
  unfold lerp
  constructor
  · apply Int.le_ediv_of_mul_le hs
    omega
  · apply Int.ediv_le_of_le_mul hs
    omega

/-- The smoothstep weight stays between its endpoints. -/
theorem fade_bounds {t s : Int} (hs : 0 < s) (ht : 0 ≤ t) (hts : t ≤ s) :
    0 ≤ fade t s ∧ fade t s ≤ s := by
  have hss : 0 < s * s := Int.mul_pos hs hs
  unfold fade
  constructor
  · apply Int.ediv_nonneg
    · exact Int.mul_nonneg (Int.mul_nonneg ht ht) (by omega)
    · omega
  · apply Int.ediv_le_of_le_mul hss
    -- s³ - t²(3s - 2t) = (s - t)²(s + 2t) ≥ 0
    have key : s * (s * s) - t * t * (3 * s - 2 * t) = (s - t) * (s - t) * (s + 2 * t) := by
      grind
    have : 0 ≤ (s - t) * (s - t) * (s + 2 * t) :=
      Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega)
    omega

theorem valueNoise_bounds (seed : UInt64) {cell : Int} (hc : 0 < cell) (x z : Int) :
    0 ≤ valueNoise seed cell x z ∧ valueNoise seed cell x z ≤ 255 := by
  have hx := fade_bounds hc (Int.emod_nonneg x (by omega)) (Int.le_of_lt (Int.emod_lt_of_pos x hc))
  have hz := fade_bounds hc (Int.emod_nonneg z (by omega)) (Int.le_of_lt (Int.emod_lt_of_pos z hc))
  unfold valueNoise
  exact lerp_bounds hc hz.1 hz.2
    (lerp_bounds hc hx.1 hx.2 (lattice_bounds ..) (lattice_bounds ..))
    (lerp_bounds hc hx.1 hx.2 (lattice_bounds ..) (lattice_bounds ..))

/-- The ground is between `minHeight` and `maxHeight` everywhere. -/
theorem height_bounds (seed : UInt64) (x z : Int) :
    minHeight ≤ height seed x z ∧ height seed x z ≤ maxHeight := by
  have h1 := valueNoise_bounds seed (cell := 128) (by decide) x z
  have h2 := valueNoise_bounds (seed + 1) (cell := 64) (by decide) x z
  have h3 := valueNoise_bounds (seed + 2) (cell := 32) (by decide) x z
  have h4 := valueNoise_bounds (seed + 3) (cell := 16) (by decide) x z
  simp only [height, minHeight, maxHeight]
  omega

/-! ## Chunk generation -/

theorem columnHeights_get (seed : UInt64) (c : ChunkPos) (l : LocalPos) :
    (columnHeights seed c)[columnIndex l] = height seed (c.blockAt l).x (c.blockAt l).z := by
  have := l.x.isLt
  have := l.z.isLt
  simp only [columnHeights, columnIndex, Fin.getElem_fin, Vector.getElem_ofFn, ChunkPos.blockAt]
  congr 2 <;> omega

/-- The chunk generator agrees with the pointwise terrain at every block. -/
theorem generateChunk_get (seed : UInt64) (c : ChunkPos) (l : LocalPos) :
    (generateChunk seed c).get l = generate seed (c.blockAt l) := by
  unfold generateChunk
  split
  · rw [Chunk.get_ofFn]
  · simp only [Chunk.get_ofFn, columnHeights_get, generate]

/-! ## Shape of the generated world -/

theorem generate_bedrock (seed : UInt64) (x z : Int) : generate seed ⟨x, 0, z⟩ = .bedrock := by
  simp [generate, generateWith]

theorem generate_below (seed : UInt64) {p : BlockPos} (h : p.y < 0) : generate seed p = .air := by
  simp [generate, generateWith, h]

/-- Nothing is generated above the tallest possible tree on the highest possible ground. -/
theorem generate_above (seed : UInt64) {p : BlockPos} (h : maxHeight + maxTreeHeight < p.y) :
    generate seed p = .air := by
  have : ¬ p.y < 0 := by simp only [maxHeight, maxTreeHeight] at h; omega
  have : ¬ p.y = 0 := by simp only [maxHeight, maxTreeHeight] at h; omega
  have : ¬ p.y ≤ minHeight - 4 := by simp only [maxHeight, maxTreeHeight, minHeight] at h ⊢; omega
  simp [generate, generateWith, *]

/-- Nothing is generated more than `maxTreeHeight` above the ground of its own column. -/
theorem generate_above_column (seed : UInt64) {p : BlockPos}
    (h : height seed p.x p.z + maxTreeHeight < p.y) : generate seed p = .air := by
  have hb := height_bounds seed p.x p.z
  simp only [minHeight, maxHeight, maxTreeHeight] at h hb
  have h1 : ¬ p.y < 0 := by omega
  have h2 : ¬ p.y = 0 := by omega
  have h3 : ¬ p.y ≤ minHeight - 4 := by simp only [minHeight]; omega
  have h4 : ¬ p.y ≤ height seed p.x p.z := by omega
  have h5 : height seed p.x p.z + maxTreeHeight < p.y := by simp only [maxTreeHeight]; omega
  simp only [generate, generateWith, blockWithHeight, h1, h2, h3, h4, h5, ite_false, ite_true,
    ite_self]

theorem ground_isSolid (h y : Int) : (ground h y).isSolid = true := by
  unfold ground
  repeat' split
  all_goals rfl

/-- From bedrock up to the surface, every block of a column is solid: the ground has no holes. -/
theorem generate_isSolid_of_le_height (seed : UInt64) {p : BlockPos} (h0 : 0 ≤ p.y)
    (h : p.y ≤ height seed p.x p.z) : (generate seed p).isSolid = true := by
  have hb := height_bounds seed p.x p.z
  simp only [generate, generateWith, blockWithHeight]
  have : ¬ p.y < 0 := by omega
  have : ¬ maxHeight + maxTreeHeight < p.y := by simp only [maxTreeHeight]; omega
  simp only [*, ite_false, ite_true]
  repeat' split
  all_goals first | rfl | exact ground_isSolid ..

/-- The surface block of every column is solid, so there is always somewhere to stand. -/
theorem generate_surface_isSolid (seed : UInt64) (x z : Int) :
    (generate seed ⟨x, height seed x z, z⟩).isSolid = true := by
  have hb := height_bounds seed x z
  exact generate_isSolid_of_le_height seed (by simp only [minHeight] at hb; exact Int.le_trans (by decide) hb.1)
    (Int.le_refl _)

end LeanMc.Terrain
