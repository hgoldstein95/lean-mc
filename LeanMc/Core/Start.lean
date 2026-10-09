import LeanMc.Core.Session
import LeanMc.Proofs.Generated
import LeanMc.Proofs.Session

/-!
# Starting a session

A `Session` cannot exist without a proof that its state is sound, so these are
the only ways to get one: the generated world's own starting point, or any
world with a bedrock floor together with a player and inventory that are
checked, at run time: the player clear of blocks, above the floor, within the
speed limit and right about whether they stand on something, and neither air
nor bedrock being carried.

A session also records the seed its terrain was generated from, with a proof
that it is that terrain's seed. So a saved game cannot name the wrong world.
-/

namespace LeanMc

namespace Session

/--
Start a session in a world with a bedrock floor, if the player and inventory
pass every check soundness asks for. Otherwise there is no session to start.
-/
def start? (world : World) (floor : ∀ x z, world.get ⟨x, 0, z⟩ = .bedrock) (player : Player)
    (inventory : Inventory := {}) (selected : Fin 9 := 0) (seed : Option UInt64 := none)
    (seeded : ∀ sd, seed = some sd → world.terrain = Terrain.generate sd := by simp) :
    Option Session :=
  if h : Player.blocked world.solid player.pos = false ∧ 65536 ≤ player.pos.y
      ∧ player.SpeedBounded
      ∧ player.onGround = Player.blocked world.solid (player.pos.add .y (-1))
      ∧ (∀ i : Fin 9, (inventory.slots[i].map (·.block)) ≠ some .air)
      ∧ (∀ i : Fin 9, (inventory.slots[i].map (·.block)) ≠ some .bedrock) then
    some {
      state := { world, player, inventory, selected }
      sound := {
        free := Player.blocked_eq_false_iff.mp h.1
        floor
        above := h.2.1
        speed := h.2.2.1
        grounded := h.2.2.2.1
        items := fun i s hs e => h.2.2.2.2.1 i (by simp [hs, e])
        bedrock := fun i s hs e => h.2.2.2.2.2 i (by simp [hs, e]) }
      seed
      seeded }
  else none

/--
Change one block outside the game's rules, as when setting up a test scene. It
is refused if it would touch the floor or leave the player inside something.
The player is told afresh whether they stand on something.
-/
def edit? (s : Session) (p : BlockPos) (b : Block) : Option Session :=
  if hp : p.y = 0 then none
  else
    let world := s.state.world.set p b
    let floor : ∀ x z, world.get ⟨x, 0, z⟩ = .bedrock := fun x z => by
      rw [World.get_set_of_ne _ _ (fun e => hp (by rw [← e]))]
      exact s.sound.floor x z
    let player := { s.state.player with
      onGround := Player.blocked world.solid (s.state.player.pos.add .y (-1)) }
    (start? world floor player s.state.inventory s.state.selected s.seed s.seeded).map
      fun started =>
      { started with pending := s.pending, debt := s.debt }

end Session

namespace Terrain

/-- The session a new game starts in. -/
def session (seed : UInt64) : Session where
  state := initial seed
  sound := initial_sound seed
  seed := some seed
  seeded sd h := by
    cases h
    rfl

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
