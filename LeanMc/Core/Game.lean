import LeanMc.Core.World
import LeanMc.Core.Player
import LeanMc.Core.Ray
import LeanMc.Core.Inventory

/-!
# The game

The whole simulated state, and the one function that advances it. A tick may
change one block, the one the player is digging or placing, and then moves the
player through the resulting world.

Blocks are conserved: digging puts the block in the inventory, and placing
takes one out of the selected slot. Nothing is created or destroyed.

A tick changes at most one block, so a command asks for at most one change: it
carries an `Action`, not a flag for each. A command that asks to dig and place
at once cannot be written down, so neither request can hide the other.
-/

namespace LeanMc

/-- What a tick can do to the world. -/
inductive Action where
  /-- Remove the block being looked at and pick it up. -/
  | dig
  /-- Put a block from the selected slot against the face being looked at. -/
  | place
  deriving DecidableEq, Repr

/-- Everything the player asks for in one tick. -/
structure Command where
  move : Input := {}
  /-- From the eyes towards what the player is looking at, in units. -/
  look : Vec3 := ⟨0, 0, 0⟩
  /-- Dig or place, if either. -/
  action : Option Action := none
  /-- Make this the selected slot. -/
  select : Option (Fin 9) := none
  deriving Repr

namespace Command

/-- Whether the command asks to dig. -/
def dig (c : Command) : Bool :=
  c.action == some .dig

/-- Whether the command asks to place. -/
def place (c : Command) : Bool :=
  c.action == some .place

end Command

structure State where
  world : World
  player : Player
  inventory : Inventory := {}
  /-- The slot that placing takes from. -/
  selected : Fin 9 := 0

/-- What a command changes, apart from moving the player. -/
structure Change where
  /-- The cell that changes. -/
  pos : BlockPos
  /-- What it becomes. -/
  block : Block
  /-- The inventory afterwards. -/
  inventory : Inventory

namespace State

/-- How far the player can reach along each axis: five blocks. -/
def reach : Int := 327680

def eye (s : State) : Vec3 :=
  s.player.pos.add .y Player.eyeHeight

/-- One component of a look vector whose longest component is `longest`, scaled so that the longest is `reach`. -/
def scaleToReach (c : Int) (longest : Nat) : Int :=
  let size : Int := ((c.natAbs * 327680 / longest : Nat) : Int)
  if c < 0 then -size else size

/--
A look vector cut down to the player's reach. One that is already within reach
along every axis is left alone; a longer one is scaled down, keeping its
direction, until its longest component is exactly the reach. Cutting each axis
down separately would instead turn the vector, towards a diagonal.
-/
def reachVector (look : Vec3) : Vec3 :=
  let longest := max look.x.natAbs (max look.y.natAbs look.z.natAbs)
  if longest ≤ 327680 then look
  else ⟨scaleToReach look.x longest, scaleToReach look.y longest, scaleToReach look.z longest⟩

/-- The block the player is looking at, if one is within reach. -/
def target (s : State) (look : Vec3) : Option RayHit :=
  Ray.cast s.world.solid s.eye (reachVector look)

/-- The slot in use this tick: the one the command selects, else the one already selected. -/
def slot (s : State) (cmd : Command) : Fin 9 :=
  cmd.select.getD s.selected

/--
What a command changes this tick, if anything.

Digging removes the targeted block and puts it in the inventory; it is refused
for bedrock and when there is no room. Placing moves one block from the
selected slot to the cell in front of the targeted face; it is refused when the
slot is empty or the player is standing in that cell.
-/
def change (s : State) (cmd : Command) : Option Change :=
  match s.target cmd.look with
  | none => none
  | some hit =>
    match cmd.action with
    | none => none
    | some .dig =>
      if s.world.get hit.block = .bedrock then none
      else
        match s.inventory.add (s.world.get hit.block) with
        | some inventory => some ⟨hit.block, .air, inventory⟩
        | none => none
    | some .place =>
      match hit.face, s.inventory.take (s.slot cmd) with
      | some f, some (b, inventory) =>
        if (Player.box s.player.pos).Overlaps (hit.block.step f) then none
        else some ⟨hit.block.step f, b, inventory⟩
      | _, _ => none

/-- The block change a command asks for this tick, if any: which cell, and what it becomes. -/
def edit (s : State) (cmd : Command) : Option (BlockPos × Block) :=
  (s.change cmd).map fun c => (c.pos, c.block)

/-- Advance the game by one tick. -/
def step (s : State) (cmd : Command) : State :=
  let world :=
    match s.change cmd with
    | some c => s.world.set c.pos c.block
    | none => s.world
  { world
    player := s.player.step world.solid cmd.move
    inventory :=
      match s.change cmd with
      | some c => c.inventory
      | none => s.inventory
    selected := s.slot cmd }

/-- Play a sequence of commands. -/
def run (s : State) (cmds : List Command) : State :=
  cmds.foldl step s

end State

end LeanMc
