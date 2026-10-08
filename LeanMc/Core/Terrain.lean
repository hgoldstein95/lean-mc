import LeanMc.Core.Chunk

/-!
# Terrain

Terrain is a function from a seed and a position to a block. It is defined at
every position and consults nothing but its arguments, so the world looks the
same whatever order it is explored in.

All arithmetic is over unbounded integers. Hills come from value noise: random
values on a coarse grid, smoothly interpolated, summed over several grid sizes.
Trees are also defined pointwise: a block is a leaf if it lies in the canopy of
some tree rooted in a nearby column.
-/

namespace LeanMc.Terrain

/-! ## Hashing -/

/-- A bijective scrambling of 64-bit values (the finaliser of SplitMix64). -/
def mix (h : UInt64) : UInt64 :=
  let h := (h ^^^ (h >>> 30)) * 0xbf58476d1ce4e5b9
  let h := (h ^^^ (h >>> 27)) * 0x94d049bb133111eb
  h ^^^ (h >>> 31)

/-- A pseudo-random value for a column of the world. Coordinates wrap modulo `2^64`. -/
def hash (seed : UInt64) (x z : Int) : UInt64 :=
  mix (mix (seed ^^^ x.toInt64.toUInt64) + z.toInt64.toUInt64 * 0x9e3779b97f4a7c15)

/-! ## Value noise -/

/-- The random value at a grid point, in `[0, 255]`. -/
def lattice (seed : UInt64) (x z : Int) : Int :=
  ((hash seed x z).toNat % 256 : Nat)

/-- The point `t / s` of the way from `a` to `b`. -/
def lerp (a b t s : Int) : Int :=
  (a * (s - t) + b * t) / s

/-- Smoothstep on `[0, s]`: eases in and out so that grid lines do not show as creases. -/
def fade (t s : Int) : Int :=
  t * t * (3 * s - 2 * t) / (s * s)

/-- Smooth noise in `[0, 255]` that varies over distances of about `cell` blocks. -/
def valueNoise (seed : UInt64) (cell x z : Int) : Int :=
  let cx := x / cell
  let cz := z / cell
  let tx := fade (x % cell) cell
  let tz := fade (z % cell) cell
  lerp
    (lerp (lattice seed cx cz) (lattice seed (cx + 1) cz) tx cell)
    (lerp (lattice seed cx (cz + 1)) (lattice seed (cx + 1) (cz + 1)) tx cell)
    tz cell

/-! ## Shape of the land -/

def minHeight : Int := 8
def maxHeight : Int := 104

/-- Ground lower than this is sand rather than grass. -/
def sandLevel : Int := 46

/-- Trees never reach further than this above the ground they stand on. -/
def maxTreeHeight : Int := 8

/-- Height of the topmost ground block in a column. -/
def height (seed : UInt64) (x z : Int) : Int :=
  let n := 8 * valueNoise seed 128 x z + 4 * valueNoise (seed + 1) 64 x z
    + 2 * valueNoise (seed + 2) 32 x z + valueNoise (seed + 3) 16 x z
  minHeight + n * (maxHeight - minHeight) / (15 * 255)

/-- The block at height `y` of a column whose ground is `h` high, for `0 < y ≤ h`. -/
def ground (h y : Int) : Block :=
  if y ≤ h - 4 then .stone
  else if h < sandLevel then .sand
  else if y < h then .dirt
  else .grass

/-! ## Trees -/

/-- If a tree is rooted in this column: the height of its ground and of its trunk. -/
def treeAt (seed : UInt64) (x z : Int) : Option (Int × Int) :=
  let r := hash (seed + 4) x z
  if r % 173 = 0 then
    let h := height seed x z
    if sandLevel ≤ h then some (h, ((4 + (r >>> 8).toNat % 3 : Nat) : Int)) else none
  else none

/-- Whether `p` lies in the leaves of a tree rooted in column `(tx, tz)`. -/
def inCanopy (seed : UInt64) (p : BlockPos) (tx tz : Int) : Bool :=
  match treeAt seed tx tz with
  | none => false
  | some (h, trunk) =>
    let dy := p.y - (h + trunk)
    let dx := (p.x - tx).natAbs
    let dz := (p.z - tz).natAbs
    if dy = -2 ∨ dy = -1 then dx ≤ 2 && dz ≤ 2 && !(dx == 2 && dz == 2 && dy == -1)
    else if dy = 0 ∨ dy = 1 then dx ≤ 1 && dz ≤ 1 && !(dx == 1 && dz == 1 && dy == 1)
    else false

def canopyReach : List Int := [-2, -1, 0, 1, 2]

/-- The block at a position above the ground: part of a tree, or air. -/
def aboveGround (seed : UInt64) (p : BlockPos) : Block :=
  let trunk : Bool :=
    match treeAt seed p.x p.z with
    | some (h, trunk) => decide (p.y ≤ h + trunk)
    | none => false
  if trunk then .log
  else if canopyReach.any fun dx => canopyReach.any fun dz => inCanopy seed p (p.x + dx) (p.z + dz)
  then .leaves
  else .air

/-! ## The terrain function -/

/--
The block at `p`, given the height `h` of the ground in its column. Trees are
cut off `maxTreeHeight` above the ground beneath each block, which bounds how
far up the search for a canopy has to go.
-/
def blockWithHeight (seed : UInt64) (h : Int) (p : BlockPos) : Block :=
  if p.y ≤ h then ground h p.y
  else if h + maxTreeHeight < p.y then .air
  else aboveGround seed p

/--
The block at `p`, with the height of its column supplied on demand.

The first tests settle most of the world without asking for the height:
nothing lies below bedrock, everything far below the lowest ground is stone,
and everything above the tallest possible tree is air.
-/
def generateWith (seed : UInt64) (columnHeight : Unit → Int) (p : BlockPos) : Block :=
  if p.y < 0 then .air
  else if p.y = 0 then .bedrock
  else if p.y ≤ minHeight - 4 then .stone
  else if maxHeight + maxTreeHeight < p.y then .air
  else blockWithHeight seed (columnHeight ()) p

/-- The block at `p` in the world generated from `seed`. -/
def generate (seed : UInt64) (p : BlockPos) : Block :=
  generateWith seed (fun _ => height seed p.x p.z) p

/-- The ground height of each of a chunk's `16 × 16` columns, indexed by `x + 16 * z`. -/
def columnHeights (seed : UInt64) (c : ChunkPos) : Vector Int 256 :=
  Vector.ofFn fun i =>
    height seed (16 * c.x + ((i.val % 16 : Nat) : Int)) (16 * c.z + ((i.val / 16 : Nat) : Int))

/-- Index of a local position's column in `columnHeights`. -/
def columnIndex (l : LocalPos) : Fin 256 :=
  ⟨l.x.val + 16 * l.z.val, by have := l.x.isLt; have := l.z.isLt; omega⟩

/--
A whole chunk of generated terrain. It computes each column's height once
instead of once per block; `LeanMc.Proofs.Terrain` shows the result is exactly
`generate` at every position.
-/
def generateChunk (seed : UInt64) (c : ChunkPos) : Chunk :=
  if 16 * c.y + 15 ≤ minHeight - 4 ∨ maxHeight + maxTreeHeight < 16 * c.y then
    Chunk.ofFn fun l => generate seed (c.blockAt l)
  else
    let heights := columnHeights seed c
    Chunk.ofFn fun l => generateWith seed (fun _ => heights[columnIndex l]) (c.blockAt l)

/-! ## A flat world, for tests -/

/-- Height of the grass layer in the flat world. -/
def flatSurface : Int := 8

/--
A flat world: bedrock at the bottom, then stone, dirt and a layer of grass,
with a pillar every eight blocks so that there is something to look at.
-/
def flat (p : BlockPos) : Block :=
  if p.y < 0 then .air
  else if p.y = 0 then .bedrock
  else if p.y < flatSurface - 3 then .stone
  else if p.y < flatSurface then .dirt
  else if p.y = flatSurface then .grass
  else if p.x % 8 = 0 ∧ p.z % 8 = 0 ∧ p.y ≤ flatSurface + 1 + (p.x / 8 + p.z / 8) % 3 then
    match (p.x / 8 + 2 * (p.z / 8)) % 5 with
    | 0 => .log
    | 1 => .planks
    | 2 => .cobble
    | 3 => .sand
    | _ => .stone
  else .air

end LeanMc.Terrain
