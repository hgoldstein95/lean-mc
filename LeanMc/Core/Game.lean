import Std.Data.HashSet
import LeanMc.Core.World
import LeanMc.Core.View
import LeanMc.Core.Player
import LeanMc.Core.Entity
import LeanMc.Core.Ray
import LeanMc.Core.Inventory
import LeanMc.Proofs.Entity

/-!
# The game

The whole simulated state, and the one function that advances it. A tick may
change one block, the one the player is digging or placing, and then moves the
player and the creatures near them through the resulting world.

The world is unbounded, so only part of it is live. The chunks within
`loadRange` of the player's chunk are loaded. Which those are is a function of
the state: the game does not ask the renderer what it happens to have built.
A creature moves only while its chunk is loaded. A column of chunks gets the
creatures its world gives it once, the first time it comes into range, and the
state remembers that it has.

Whatever is random in a tick is drawn from the generator the state carries, so
a tick is a function of the state and the command and of nothing else.

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
  /-- The creatures that have been made, in the order they were made. -/
  entities : List Entity := []
  /-- The columns of chunks whose creatures have been made. -/
  populated : Std.HashSet (Int × Int) := {}
  /-- Where the next random number comes from. -/
  rng : Rng := ⟨0⟩

/-- What a command changes, apart from moving the player. -/
structure Change where
  /-- The cell that changes. -/
  pos : BlockPos
  /-- What it becomes. -/
  block : Block
  /-- The inventory afterwards. -/
  inventory : Inventory

/--
How far around the player the world is loaded, in chunks. Creatures move only
in loaded chunks, and the renderer draws the same ones.
-/
def loadRange : ViewRange := ⟨6, 4⟩

namespace State

/-- How far the player can reach along each axis: five blocks. -/
def reach : Int := 327680

def eye (s : State) : Vec3 :=
  s.player.eye

/-- The chunk the world is loaded around: the one the player's eyes are in. -/
def centre (s : State) : ChunkPos :=
  s.player.chunk

/-- Whether chunk `c` is loaded while the player is in chunk `centre`. -/
def loaded (centre c : ChunkPos) : Bool :=
  loadRange.contains centre c

/--
Make one column's creatures, unless they have been made. A creature whose
place is not sound in the world as it is now is left out.
-/
def populateColumn (world : World) (acc : List Entity × Std.HashSet (Int × Int))
    (column : Int × Int) : List Entity × Std.HashSet (Int × Int) :=
  if acc.2.contains column then acc
  else
    (acc.1 ++ (world.creatures column.1 column.2).filter fun e => decide (e.Sound world.solid),
      acc.2.insert column)

/-- The columns of chunks with a chunk loaded while the player is in chunk `centre`. -/
def loadedColumns (centre : ChunkPos) : List (Int × Int) :=
  loadRange.columns.map fun o => (centre.x + o.1, centre.z + o.2)

/--
Make the creatures of every loaded column that has not had its creatures made.
Returns the creatures there are now, new ones last, and the columns done.
-/
def populate (world : World) (centre : ChunkPos) (entities : List Entity)
    (populated : Std.HashSet (Int × Int)) : List Entity × Std.HashSet (Int × Int) :=
  (loadedColumns centre).foldl (populateColumn world) (entities, populated)

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

/-- The player or a creature is standing in the cell, so nothing can be placed there. -/
def Occupied (s : State) (p : BlockPos) : Prop :=
  (Player.box s.player.pos).Overlaps p ∨ ∃ e ∈ s.entities, (Entity.box e.pos).Overlaps p

instance (s : State) (p : BlockPos) : Decidable (s.Occupied p) := by
  unfold Occupied
  infer_instance

/-- The slot in use this tick: the one the command selects, else the one already selected. -/
def slot (s : State) (cmd : Command) : Fin 9 :=
  cmd.select.getD s.selected

/--
What a command changes this tick, if anything.

Digging removes the targeted block and puts it in the inventory; it is refused
for bedrock and when there is no room. Placing moves one block from the
selected slot to the cell in front of the targeted face; it is refused when the
slot is empty or the player or a creature is standing in that cell.
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
        if s.Occupied (hit.block.step f) then none
        else some ⟨hit.block.step f, b, inventory⟩
      | _, _ => none

/-- The block change a command asks for this tick, if any: which cell, and what it becomes. -/
def edit (s : State) (cmd : Command) : Option (BlockPos × Block) :=
  (s.change cmd).map fun c => (c.pos, c.block)

/--
Advance the game by one tick. The creatures in chunks that were loaded when the
tick began move; the rest do not. If the player ends the tick in another chunk,
the columns that have come into range are populated.
-/
def step (s : State) (cmd : Command) : State :=
  let world :=
    match s.change cmd with
    | some c => s.world.set c.pos c.block
    | none => s.world
  let moved := Entity.stepAll world.solid (fun e => loaded s.centre e.chunk) s.rng s.entities
  let player := s.player.step world.solid cmd.move
  let grown :=
    if player.chunk = s.centre then (moved.1, s.populated)
    else populate world player.chunk moved.1 s.populated
  { world
    player
    inventory :=
      match s.change cmd with
      | some c => c.inventory
      | none => s.inventory
    selected := s.slot cmd
    entities := grown.1
    populated := grown.2
    rng := moved.2 }

/-- Play a sequence of commands. -/
def run (s : State) (cmds : List Command) : State :=
  cmds.foldl step s

end State

end LeanMc
