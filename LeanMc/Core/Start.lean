import LeanMc.Core.Session
import LeanMc.Proofs.Generated
import LeanMc.Proofs.Session

/-!
# Starting a session

A `Session` cannot exist without a proof that its state is sound, so these are
the only ways to get one: the generated world's own starting point, or any
world with a bedrock floor together with a player and inventory that are
checked, at run time: the player clear of blocks and above the floor, and no
air being carried.
-/

namespace LeanMc

namespace Session

/--
Start a session in a world with a bedrock floor, if the player is clear of
solid blocks and above the floor. Otherwise there is no session to start.
-/
def start? (world : World) (floor : ∀ x z, world.get ⟨x, 0, z⟩ = .bedrock) (player : Player)
    (inventory : Inventory := {}) (selected : Fin 9 := 0) : Option Session :=
  if h : Player.blocked world.solid player.pos = false ∧ 65536 ≤ player.pos.y
      ∧ ∀ i : Fin 9, (inventory.slots[i].map (·.block)) ≠ some .air then
    some {
      state := { world, player, inventory, selected }
      sound := {
        free := Player.blocked_eq_false_iff.mp h.1
        floor
        above := h.2.1
        items := fun i s hs e => h.2.2 i (by simp [hs, e]) } }
  else none

/--
Change one block outside the game's rules, as when setting up a test scene. It
is refused if it would touch the floor or leave the player inside something.
-/
def edit? (s : Session) (p : BlockPos) (b : Block) : Option Session :=
  if hp : p.y = 0 then none
  else
    let floor : ∀ x z, (s.state.world.set p b).get ⟨x, 0, z⟩ = .bedrock := fun x z => by
      rw [World.get_set_of_ne _ _ (fun e => hp (by rw [← e]))]
      exact s.sound.floor x z
    (start? (s.state.world.set p b) floor s.state.player s.state.inventory s.state.selected).map
      fun started =>
      { started with pending := s.pending, debt := s.debt }

end Session

namespace Terrain

/-- The session a new game starts in. -/
def session (seed : UInt64) : Session where
  state := initial seed
  sound := initial_sound seed

theorem world_floor_get (seed : UInt64) (x z : Int) :
    (world seed).get ⟨x, 0, z⟩ = .bedrock := by
  simp [generate_bedrock]

/-- The flat test world. -/
def flatWorld : World :=
  World.new flat

theorem flatWorld_floor (x z : Int) : flatWorld.get ⟨x, 0, z⟩ = .bedrock := by
  simp [flatWorld, flat]

/--
**The game never goes wrong, frame by frame.** Whatever frames arrive, at
whatever rate and with whatever input, the player is never inside a solid
block, the bedrock floor is never broken, and the player never falls through
it.
-/
theorem session_sound (seed : UInt64) (frames : List Frame) :
    ((session seed).play frames).1.state.Sound :=
  Session.play_sound _ frames

end Terrain

end LeanMc
