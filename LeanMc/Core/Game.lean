import LeanMc.Core.World
import LeanMc.Core.Player
import LeanMc.Core.Ray

/-!
# The game

The whole simulated state, and the one function that advances it. A tick may
change one block, the one the player is digging or placing, and then moves the
player through the resulting world.
-/

namespace LeanMc

/-- Everything the player asks for in one tick. -/
structure Command where
  move : Input := {}
  /-- From the eyes towards what the player is looking at, in units. -/
  look : Vec3 := ⟨0, 0, 0⟩
  /-- Remove the block being looked at. -/
  dig : Bool := false
  /-- Put this block against the face being looked at. -/
  place : Option Block := none

structure State where
  world : World
  player : Player

namespace State

/-- How far the player can reach along each axis: five blocks. -/
def reach : Int := 327680

def eye (s : State) : Vec3 :=
  s.player.pos.add .y Player.eyeHeight

/-- A look vector cut down to the player's reach. -/
def reachVector (look : Vec3) : Vec3 :=
  ⟨Player.clamp (-reach) reach look.x, Player.clamp (-reach) reach look.y,
   Player.clamp (-reach) reach look.z⟩

/-- The block the player is looking at, if one is within reach. -/
def target (s : State) (look : Vec3) : Option RayHit :=
  Ray.cast s.world.solid s.eye (reachVector look)

/--
The block change a command asks for this tick, if any.

Digging removes the targeted block, except bedrock. Placing puts a block in the
cell in front of the targeted face, unless the player is standing there.
-/
def edit (s : State) (cmd : Command) : Option (BlockPos × Block) :=
  match s.target cmd.look with
  | none => none
  | some hit =>
    if cmd.dig then
      if s.world.get hit.block = .bedrock then none else some (hit.block, .air)
    else
      match cmd.place, hit.face with
      | some b, some f =>
        if (Player.box s.player.pos).Overlaps (hit.block.step f) then none
        else some (hit.block.step f, b)
      | _, _ => none

/-- Advance the game by one tick. -/
def step (s : State) (cmd : Command) : State :=
  let world :=
    match s.edit cmd with
    | some (p, b) => s.world.set p b
    | none => s.world
  { world, player := s.player.step world.solid cmd.move }

/-- Play a sequence of commands. -/
def run (s : State) (cmds : List Command) : State :=
  cmds.foldl step s

end State

end LeanMc
