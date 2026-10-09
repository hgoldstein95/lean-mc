import LeanMc.Core.World
import LeanMc.Core.Player
import LeanMc.Core.Game
import LeanMc.Proofs.Terrain

/-!
# The generated world

The world the game is played in: generated terrain, with the fast chunk
generator standing in for block-by-block evaluation, and the foxes that live
on it.

Foxes are part of the terrain's generation. Like trees, they are a function of
the seed and of where they are, so the world has the same foxes whatever order
it is explored in.
-/

namespace LeanMc.Terrain

/-- Whether the generated terrain is solid at `p`. -/
def solid (seed : UInt64) (p : BlockPos) : Bool :=
  (generate seed p).isSolid

/--
Where a newcomer to the column of blocks at `(x, z)` starts looking for a place
to stand: the middle of the column, above the tallest tree that could grow
there.
-/
def dropPoint (seed : UInt64) (x z : Int) : Vec3 :=
  ⟨x * 65536 + 32768, (height seed x z + maxTreeHeight + 1) * 65536, z * 65536 + 32768⟩

/--
Where a body of shape `sh` comes to stand in the column of blocks at `(x, z)`:
`dropPoint`, lowered onto whatever is beneath it.
-/
def standing (seed : UInt64) (sh : Shape) (x z : Int) : Vec3 :=
  sh.settle (solid seed) 16 (dropPoint seed x z)

/-- One column of chunks in this many starts with a fox. -/
def foxRarity : UInt64 := 32

/--
The creatures the column of chunks at `(cx, cz)` starts with: a fox, in one
column in `foxRarity`. It stands on the ground somewhere in the column, facing
some way, as the seed chooses.
-/
def creatures (seed : UInt64) (cx cz : Int) : List Entity :=
  let r := hash (seed + 5) cx cz
  if r % foxRarity = 0 then
    let x := 16 * cx + (((r >>> 8).toNat % 16 : Nat) : Int)
    let z := 16 * cz + (((r >>> 16).toNat % 16 : Nat) : Int)
    [Entity.resting (solid seed) (standing seed Entity.shape x z) (Entity.pickHeading (r >>> 24))]
  else []

/-- The untouched world generated from `seed`. -/
def world (seed : UInt64) : World :=
  World.newWithChunks (generate seed) (generateChunk seed) (generateChunk_get seed)
    (creatures seed)

/-- Where a new player stands: in the column of blocks at the origin. -/
def spawn (seed : UInt64) : Vec3 :=
  standing seed Player.shape 0 0

/-- A new player: standing at `spawn`, knowing whether there is something to stand on. -/
def newcomer (seed : UInt64) : Player :=
  Player.resting (solid seed) (spawn seed)

/-- The state a new game starts in, with the creatures of the loaded columns made. -/
def initial (seed : UInt64) : State where
  world := world seed
  player := newcomer seed
  entities := (State.populate (world seed) (newcomer seed).chunk [] {}).1
  populated := (State.populate (world seed) (newcomer seed).chunk [] {}).2
  rng := .ofSeed seed

end LeanMc.Terrain

namespace LeanMc.World

/-- The world is the one generated from `seed`, edits aside: it has that terrain and those creatures. -/
def FromSeed (w : World) (seed : UInt64) : Prop :=
  w.terrain = Terrain.generate seed ∧ w.creatures = Terrain.creatures seed

end LeanMc.World
