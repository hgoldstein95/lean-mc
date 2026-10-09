import LeanMc.Core.Mesh
import LeanMc.Proofs.World

/-!
# Meshing theorems

* **Soundness and completeness.** A chunk's mesh contains a face exactly when
  the block there is visible and its neighbour on that side does not hide it.
  Nothing is drawn that should not be, and nothing visible is left out,
  including at the seams between chunks.
* **No duplicates.** Each such face appears exactly once.
* **Locality.** A chunk's mesh depends only on its own blocks and the blocks
  touching its sides. So an edit can change the meshes of the chunk it is in
  and the chunks it touches, and no others.
* **Cache independence.** Meshing through a valid chunk cache gives the same
  result as meshing from the world.
* **Buffer layout.** The packed buffer is exactly the listed faces, six
  vertices of eight bytes each, and every field fits its byte without wrapping.
  A chunk's mesh is never more than 147456 vertices, well within the counts the
  shim keeps in 32 bits.
* **Face geometry.** The table of face corners is real geometry: every corner
  of a face lies on that face of the block, both triangles are wound
  counter-clockwise seen from outside, so they face outwards and are not
  culled, and the texture on a side face is the right way up.
-/

namespace LeanMc

/-! ## Directions -/

namespace Dir

theorem nodup_all : all.Nodup := by decide

theorem opp_opp (d : Dir) : d.opp.opp = d := by cases d <;> rfl

theorem toNat_lt (d : Dir) : d.toNat < 6 := by cases d <;> decide

end Dir

namespace BlockPos

theorem step_step_opp (p : BlockPos) (d : Dir) : (p.step d).step d.opp = p := by
  cases d <;> ext <;> simp [step, Dir.opp] <;> omega

theorem eq_step_opp_of_step_eq {p q : BlockPos} {d : Dir} (h : q.step d = p) :
    q = p.step d.opp := by
  rw [← h, step_step_opp]

end BlockPos

namespace LocalPos

theorem nodup_all : all.Nodup := by
  unfold all List.Nodup
  rw [List.pairwise_map]
  refine (List.nodup_finRange 4096).imp ?_
  intro i j hij h
  exact hij (by rw [← index_ofIndex i, ← index_ofIndex j, h])

end LocalPos

/-! ## Which faces are in a mesh -/

theorem mem_blockFaces {blockAt : BlockPos → Block} {c : ChunkPos} {l : LocalPos} {f : Face} :
    f ∈ blockFaces blockAt c l ↔
      f.pos = l ∧ faceVisible blockAt (c.blockAt l) f.dir = true
        ∧ f.block = blockAt (c.blockAt l) := by
  simp only [blockFaces, List.mem_filterMap]
  constructor
  · rintro ⟨d, -, h⟩
    split at h
    · next hv =>
      cases h
      exact ⟨rfl, hv, rfl⟩
    · cases h
  · rintro ⟨rfl, hv, hb⟩
    refine ⟨f.dir, Dir.mem_all _, ?_⟩
    simp [hv, ← hb]

/--
**Soundness and completeness of meshing.** A face is in a chunk's mesh exactly
when it should be drawn: its block is visible, the neighbouring block on that
side is not opaque, and it carries that block's type.
-/
theorem mem_chunkFaces {blockAt : BlockPos → Block} {c : ChunkPos} {f : Face} :
    f ∈ chunkFaces blockAt c ↔
      faceVisible blockAt (c.blockAt f.pos) f.dir = true
        ∧ f.block = blockAt (c.blockAt f.pos) := by
  simp only [chunkFaces, List.mem_flatMap, mem_blockFaces]
  constructor
  · rintro ⟨l, -, rfl, h⟩
    exact h
  · intro h
    exact ⟨f.pos, LocalPos.mem_all _, rfl, h⟩

/-- Every face that should be drawn is in the mesh: there are no holes. -/
theorem face_mem_chunkFaces {blockAt : BlockPos → Block} {c : ChunkPos} (l : LocalPos) (d : Dir)
    (h : faceVisible blockAt (c.blockAt l) d = true) :
    ⟨l, d, blockAt (c.blockAt l)⟩ ∈ chunkFaces blockAt c :=
  mem_chunkFaces.mpr ⟨h, rfl⟩

theorem nodup_blockFaces (blockAt : BlockPos → Block) (c : ChunkPos) (l : LocalPos) :
    (blockFaces blockAt c l).Nodup := by
  unfold blockFaces
  refine List.Pairwise.filterMap _ ?_ Dir.nodup_all
  intro d d' hne f hf f' hf' heq
  split at hf
  · split at hf'
    · cases hf
      cases hf'
      exact hne (congrArg Face.dir heq)
    · cases hf'
  · cases hf

/-- No face is emitted twice, so no two triangles of a mesh ever coincide. -/
theorem nodup_chunkFaces (blockAt : BlockPos → Block) (c : ChunkPos) :
    (chunkFaces blockAt c).Nodup := by
  unfold chunkFaces List.Nodup
  rw [List.pairwise_flatMap]
  refine ⟨fun l _ => nodup_blockFaces blockAt c l, LocalPos.nodup_all.imp ?_⟩
  intro l l' hne f hf f' hf' heq
  apply hne
  rw [← (mem_blockFaces.mp hf).1, ← (mem_blockFaces.mp hf').1, heq]

/-! ## What a mesh depends on -/

/--
A chunk's mesh depends only on the blocks inside the chunk and the blocks one
step outside it.
-/
theorem chunkFaces_congr {blockAt blockAt' : BlockPos → Block} {c : ChunkPos}
    (hin : ∀ l, blockAt (c.blockAt l) = blockAt' (c.blockAt l))
    (hadj : ∀ l d, blockAt ((c.blockAt l).step d) = blockAt' ((c.blockAt l).step d)) :
    chunkFaces blockAt c = chunkFaces blockAt' c := by
  unfold chunkFaces
  congr 1
  funext l
  have hvis : ∀ d, faceVisible blockAt (c.blockAt l) d = faceVisible blockAt' (c.blockAt l) d :=
    fun d => by simp only [faceVisible, hin l, hadj l d]
  simp only [blockFaces, hvis, hin l]

/-- Meshing through a valid chunk cache is the same as meshing from the world. -/
theorem meshChunk_cache {cache : ChunkCache} {w : World} (h : cache.Valid w) (c : ChunkPos) :
    meshChunk (cache.blockAt w) c = meshChunk w.get c := by
  have : cache.blockAt w = w.get := funext h.blockAt_eq
  rw [this]

/--
**Locality of edits.** Writing a block leaves a chunk's faces unchanged unless
the chunk contains the block or contains one of its six neighbours.
-/
theorem chunkFaces_set (w : World) (p : BlockPos) (b : Block) (c : ChunkPos)
    (hc : c ≠ p.chunkPos) (hn : ∀ d, c ≠ (p.step d).chunkPos) :
    chunkFaces (w.set p b).get c = chunkFaces w.get c := by
  apply chunkFaces_congr
  · intro l
    apply World.get_set_of_ne
    intro h
    exact hc (by rw [← h, ChunkPos.chunkPos_blockAt])
  · intro l d
    apply World.get_set_of_ne
    intro h
    apply hn d.opp
    rw [← BlockPos.eq_step_opp_of_step_eq h, ChunkPos.chunkPos_blockAt]

/-- The same, for the packed buffer the renderer is given. -/
theorem meshChunk_set (w : World) (p : BlockPos) (b : Block) (c : ChunkPos)
    (hc : c ≠ p.chunkPos) (hn : ∀ d, c ≠ (p.step d).chunkPos) :
    meshChunk (w.set p b).get c = meshChunk w.get c := by
  unfold meshChunk
  rw [chunkFaces_set w p b c hc hn]

/-! ## The packed buffer -/

namespace Face

/-- The eight bytes of one packed vertex, as a specification of `pushVertex`. -/
def vertex (f : Face) (i : Fin 4) : List UInt8 :=
  [ (f.pos.x.val + (f.dir.corner i).1).toUInt8,
    (f.pos.y.val + (f.dir.corner i).2.1).toUInt8,
    (f.pos.z.val + (f.dir.corner i).2.2).toUInt8,
    (f.block.tile f.dir % 16 + (cornerUV i).1).toUInt8,
    (f.block.tile f.dir / 16 + (cornerUV i).2).toUInt8,
    f.dir.shade,
    f.dir.toNat.toUInt8,
    0 ]

/-- The 48 bytes of one packed face. -/
def bytes (f : Face) : List UInt8 :=
  triangleCorners.flatMap f.vertex

theorem toList_pushVertex (f : Face) (out : ByteArray) (i : Fin 4) :
    (f.pushVertex out i).data.toList = out.data.toList ++ f.vertex i := by
  simp [pushVertex, vertex, ByteArray.data_push]

theorem toList_push (out : ByteArray) (f : Face) :
    (push out f).data.toList = out.data.toList ++ f.bytes := by
  simp [push, bytes, triangleCorners, toList_pushVertex]

theorem length_bytes (f : Face) : f.bytes.length = 48 := by
  simp [bytes, triangleCorners, vertex]

end Face

theorem toList_foldl_push (faces : List Face) (out : ByteArray) :
    (faces.foldl Face.push out).data.toList = out.data.toList ++ faces.flatMap Face.bytes := by
  induction faces generalizing out with
  | nil => simp
  | cons f fs ih => simp [ih, Face.toList_push]

/-- The packed buffer is exactly the faces' bytes, in order. -/
theorem toList_packFaces (faces : List Face) :
    (packFaces faces).data.toList = faces.flatMap Face.bytes := by
  simp [packFaces, toList_foldl_push]

theorem length_flatMap_bytes (faces : List Face) :
    (faces.flatMap Face.bytes).length = 48 * faces.length := by
  induction faces with
  | nil => rfl
  | cons f fs ih =>
    rw [List.flatMap_cons, List.length_append, Face.length_bytes, ih, List.length_cons]
    omega

/-- The buffer holds 48 bytes per face: six vertices of eight bytes. -/
theorem size_packFaces (faces : List Face) : (packFaces faces).size = 48 * faces.length := by
  have h := congrArg List.length (toList_packFaces faces)
  rw [Array.length_toList, length_flatMap_bytes] at h
  exact h

theorem size_meshChunk (blockAt : BlockPos → Block) (c : ChunkPos) :
    (meshChunk blockAt c).size = 48 * (chunkFaces blockAt c).length :=
  size_packFaces _

/-- A whole number of triangles: the vertex count is a multiple of three. -/
theorem meshChunk_vertices (blockAt : BlockPos → Block) (c : ChunkPos) :
    (meshChunk blockAt c).size = Face.vertexBytes * (3 * (2 * (chunkFaces blockAt c).length)) := by
  rw [size_meshChunk, Face.vertexBytes]
  omega

theorem length_blockFaces_le (blockAt : BlockPos → Block) (c : ChunkPos) (l : LocalPos) :
    (blockFaces blockAt c l).length ≤ 6 :=
  List.length_filterMap_le _ _

theorem length_flatMap_le {α β : Type} (f : α → List β) (k : Nat) (h : ∀ a, (f a).length ≤ k)
    (l : List α) : (l.flatMap f).length ≤ k * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have := h a
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    omega

/-- A chunk has at most six faces for each of its 4096 blocks. -/
theorem length_chunkFaces_le (blockAt : BlockPos → Block) (c : ChunkPos) :
    (chunkFaces blockAt c).length ≤ 24576 := by
  have h := length_flatMap_le (blockFaces blockAt c) 6 (length_blockFaces_le blockAt c) LocalPos.all
  have hall : LocalPos.all.length = 4096 := by simp [LocalPos.all]
  rw [hall] at h
  exact h

/--
A chunk's mesh is at most 1179648 bytes, which is 147456 vertices: the vertex
and byte counts the shim computes from it fit in 32 bits with room to spare.
-/
theorem size_meshChunk_le (blockAt : BlockPos → Block) (c : ChunkPos) :
    (meshChunk blockAt c).size ≤ 1179648 := by
  have := length_chunkFaces_le blockAt c
  rw [size_meshChunk]
  omega

/-! ## Face geometry -/

namespace Dir

/-- The outward direction of each face, as a vector. -/
def normal : Dir → Int × Int × Int
  | xp => (1, 0, 0) | xn => (-1, 0, 0) | yp => (0, 1, 0) | yn => (0, -1, 0)
  | zp => (0, 0, 1) | zn => (0, 0, -1)

/-- A face corner as an integer vector. -/
def cornerVec (d : Dir) (i : Fin 4) : Int × Int × Int :=
  ((d.corner i).1, (d.corner i).2.1, (d.corner i).2.2)

/-- The cross product of the two edges of a triangle leaving its first corner. -/
def triangleNormal (a b c : Int × Int × Int) : Int × Int × Int :=
  let u : Int × Int × Int := (b.1 - a.1, b.2.1 - a.2.1, b.2.2 - a.2.2)
  let v : Int × Int × Int := (c.1 - a.1, c.2.1 - a.2.1, c.2.2 - a.2.2)
  (u.2.1 * v.2.2 - u.2.2 * v.2.1, u.2.2 * v.1 - u.1 * v.2.2, u.1 * v.2.1 - u.2.1 * v.1)

/--
**Every corner of a face lies on that face of the block**: on the plane one
unit along the face's direction for the positive faces, and on the plane
through the block's minimum corner for the negative ones.
-/
theorem corner_on_face (d : Dir) (i : Fin 4) :
    match d with
    | xp => (d.corner i).1 = 1 | xn => (d.corner i).1 = 0
    | yp => (d.corner i).2.1 = 1 | yn => (d.corner i).2.1 = 0
    | zp => (d.corner i).2.2 = 1 | zn => (d.corner i).2.2 = 0 := by
  cases d <;> revert i <;> decide

/-- The four corners of a face are four different points. -/
theorem corner_injective (d : Dir) (i j : Fin 4) (h : d.corner i = d.corner j) : i = j := by
  cases d <;> revert i j <;> decide

/--
**Faces are wound outwards.** Both triangles of every face, corners `0 1 2`
and `0 2 3`, turn counter-clockwise seen from outside the block: the cross
product of their edges is exactly the face's outward direction. So neither is
culled as a back face, and the direction sent to the shim is the true normal.
-/
theorem winding (d : Dir) :
    triangleNormal (d.cornerVec 0) (d.cornerVec 1) (d.cornerVec 2) = d.normal
      ∧ triangleNormal (d.cornerVec 0) (d.cornerVec 2) (d.cornerVec 3) = d.normal := by
  cases d <;> decide

/-- The corners the two triangles use are the ones `winding` is about. -/
theorem triangleCorners_eq : Face.triangleCorners = [0, 1, 2, 0, 2, 3] := rfl

/--
**Side faces are textured the right way up**: the texture's `v` runs down as
the corner's `y` runs up, so the top of the tile is at the top of the block.
-/
theorem uv_upright (d : Dir) (i : Fin 4) (h : d ≠ yp ∧ d ≠ yn) :
    (cornerUV i).2 + (d.corner i).2.1 = 1 := by
  cases d <;> revert i <;> simp at h ⊢ <;> decide

/-- Each corner of a face gets a different corner of the tile. -/
theorem cornerUV_injective (i j : Fin 4) (h : cornerUV i = cornerUV j) : i = j := by
  revert i j
  decide

end Dir

/-! ## Byte ranges -/

theorem Dir.corner_le (d : Dir) (i : Fin 4) :
    (d.corner i).1 ≤ 1 ∧ (d.corner i).2.1 ≤ 1 ∧ (d.corner i).2.2 ≤ 1 := by
  cases d <;> (revert i; decide)

theorem cornerUV_le (i : Fin 4) : (cornerUV i).1 ≤ 1 ∧ (cornerUV i).2 ≤ 1 := by
  revert i; decide

theorem Block.tile_lt (b : Block) (d : Dir) : b.tile d < 256 := by
  cases b <;> cases d <;> decide

/--
No field of a packed vertex wraps around: read back as numbers, the bytes are
the block corner's position, its texture corner, its shade and its direction.
-/
theorem Face.toNat_vertex (f : Face) (i : Fin 4) :
    (f.vertex i).map UInt8.toNat =
      [ f.pos.x.val + (f.dir.corner i).1,
        f.pos.y.val + (f.dir.corner i).2.1,
        f.pos.z.val + (f.dir.corner i).2.2,
        f.block.tile f.dir % 16 + (cornerUV i).1,
        f.block.tile f.dir / 16 + (cornerUV i).2,
        f.dir.shade.toNat,
        f.dir.toNat,
        0 ] := by
  have := f.pos.x.isLt
  have := f.pos.y.isLt
  have := f.pos.z.isLt
  have := Dir.corner_le f.dir i
  have := cornerUV_le i
  have := Block.tile_lt f.block f.dir
  have := f.dir.toNat_lt
  have hx : (f.pos.x.val + (f.dir.corner i).1) % 256 = f.pos.x.val + (f.dir.corner i).1 :=
    Nat.mod_eq_of_lt (by omega)
  have hy : (f.pos.y.val + (f.dir.corner i).2.1) % 256 = f.pos.y.val + (f.dir.corner i).2.1 :=
    Nat.mod_eq_of_lt (by omega)
  have hz : (f.pos.z.val + (f.dir.corner i).2.2) % 256 = f.pos.z.val + (f.dir.corner i).2.2 :=
    Nat.mod_eq_of_lt (by omega)
  have hu : (f.block.tile f.dir % 16 + (cornerUV i).1) % 256
      = f.block.tile f.dir % 16 + (cornerUV i).1 := Nat.mod_eq_of_lt (by omega)
  have hv : (f.block.tile f.dir / 16 + (cornerUV i).2) % 256
      = f.block.tile f.dir / 16 + (cornerUV i).2 := Nat.mod_eq_of_lt (by omega)
  have hd : f.dir.toNat % 256 = f.dir.toNat := Nat.mod_eq_of_lt (by omega)
  simp [vertex, hx, hy, hz, hu, hv, hd]

end LeanMc
