import LeanMc.Core.Block
import LeanMc.Core.Pos

/-!
# Terrain

Terrain is a function from position to block, so it is defined everywhere and
does not depend on the order in which the world is explored.
-/

namespace LeanMc.Terrain

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
