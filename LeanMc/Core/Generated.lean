import LeanMc.Core.World
import LeanMc.Core.Player
import LeanMc.Core.Game
import LeanMc.Core.Session
import LeanMc.Proofs.Terrain

/-!
# The generated world

The world the game is played in: generated terrain, with the fast chunk
generator standing in for block-by-block evaluation.
-/

namespace LeanMc.Terrain

/-- The untouched world generated from `seed`. -/
def world (seed : UInt64) : World :=
  World.newWithChunks (generate seed) (generateChunk seed) (generateChunk_get seed)

/--
Where a new player starts looking for a place to stand: the middle of the
column at the origin, above the tallest tree that could grow there.
-/
def spawnStart (seed : UInt64) : Vec3 :=
  ⟨32768, (height seed 0 0 + maxTreeHeight + 1) * 65536, 32768⟩

/-- Where a new player stands: `spawnStart`, lowered onto whatever is beneath it. -/
def spawn (seed : UInt64) : Vec3 :=
  Player.settle (world seed).solid 16 (spawnStart seed)

/-- The state a new game starts in. -/
def initial (seed : UInt64) : State where
  world := world seed
  player := { pos := spawn seed }

/-- The session a new game starts in: the initial state, nothing waiting, no time owed. -/
def session (seed : UInt64) : Session where
  state := initial seed

end LeanMc.Terrain
