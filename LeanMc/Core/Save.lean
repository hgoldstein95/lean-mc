import LeanMc.Core.Start

/-!
# Saving and loading

A saved game is plain data: the world's seed, the player, what they carry, and
the list of blocks that differ from the generated terrain. It is written as a
list of integers.

Loading trusts nothing. The integers must parse, and the game they describe
must pass the same checks as any other way of starting a session: an intact
floor; a player who is clear of blocks, above the floor, within the speed limit
and right about whether they stand on something; and neither air nor bedrock
being carried. A file that fails is refused; it cannot produce an unsound game.

A session knows the seed its terrain came from, so saving takes no seed from
outside: the file cannot name a world other than the one being played.

`LeanMc.Proofs.Save` shows that encoding loses nothing, and that a game saved
and loaded is the same game.
-/

namespace LeanMc

namespace Block

/-- A number for each block, for saved games. Zero is air. -/
def toNat : Block → Nat
  | air => 0 | bedrock => 1 | stone => 2 | dirt => 3 | grass => 4 | sand => 5
  | log => 6 | leaves => 7 | planks => 8 | cobble => 9

def ofNat? : Nat → Option Block
  | 0 => some air | 1 => some bedrock | 2 => some stone | 3 => some dirt | 4 => some grass
  | 5 => some sand | 6 => some log | 7 => some leaves | 8 => some planks | 9 => some cobble
  | _ => none

end Block

/-- Everything needed to rebuild a game. -/
structure SaveData where
  seed : UInt64
  player : Player
  inventory : Inventory
  selected : Fin 9
  /--
  Every cell that has ever been written, with what it holds now. A cell that
  was dug and filled in again is listed although it matches the terrain.
  -/
  edits : List (BlockPos × Block)
  deriving DecidableEq, Repr

namespace SaveData

/-- Marks the start of a saved game, and its format version. -/
def magic : Int := 7707
def version : Int := 1

def encodeBool (b : Bool) : Int :=
  if b then 1 else 0

def decodeBool? (n : Int) : Option Bool :=
  if n = 0 then some false else if n = 1 then some true else none

/-- A slot as two integers: block and count, or two zeros for an empty slot. -/
def encodeSlot : Option Stack → List Int
  | none => [0, 0]
  | some s => [(s.block.toNat : Int), (s.count : Int)]

def decodeSlot? (block count : Int) : Option (Option Stack) :=
  if count = 0 then (if block = 0 then some none else none)
  else if h : 1 ≤ count ∧ count ≤ 64 then
    (Block.ofNat? block.toNat).bind fun b =>
      if 0 ≤ block then some (some ⟨b, ⟨(count - 1).toNat, by omega⟩⟩) else none
  else none

/-- Read `n` slots from the front of a list of integers, returning the rest. -/
def decodeSlots? : Nat → List Int → Option (List (Option Stack) × List Int)
  | 0, rest => some ([], rest)
  | n + 1, block :: count :: rest =>
    (decodeSlot? block count).bind fun slot =>
      (decodeSlots? n rest).map fun (slots, rest) => (slot :: slots, rest)
  | _ + 1, _ => none

def encodeEdit (e : BlockPos × Block) : List Int :=
  [e.1.x, e.1.y, e.1.z, (e.2.toNat : Int)]

/-- Read `n` edits from the front of a list of integers; nothing may be left over. -/
def decodeEdits? : Nat → List Int → Option (List (BlockPos × Block))
  | 0, [] => some []
  | 0, _ :: _ => none
  | n + 1, x :: y :: z :: block :: rest =>
    if 0 ≤ block then
      (Block.ofNat? block.toNat).bind fun b =>
        (decodeEdits? n rest).map fun edits => (⟨x, y, z⟩, b) :: edits
    else none
  | _ + 1, _ => none

/-- A saved game as a list of integers. -/
def encode (d : SaveData) : List Int :=
  [magic, version, (d.seed.toNat : Int),
   d.player.pos.x, d.player.pos.y, d.player.pos.z,
   d.player.vel.x, d.player.vel.y, d.player.vel.z,
   encodeBool d.player.onGround, encodeBool d.player.flying, (d.selected.val : Int)]
    ++ d.inventory.slots.toList.flatMap encodeSlot
    ++ (d.edits.length : Int) :: d.edits.flatMap encodeEdit

/-- Read a saved game back. Anything malformed gives `none`. -/
def decode? : List Int → Option SaveData
  | m :: v :: seed :: px :: py :: pz :: vx :: vy :: vz :: ground :: flying :: selected :: rest =>
    if m = magic ∧ v = version ∧ 0 ≤ seed ∧ seed < 18446744073709551616 then
      if hs : 0 ≤ selected ∧ selected < 9 then
        (decodeBool? ground).bind fun onGround =>
        (decodeBool? flying).bind fun flying =>
        (decodeSlots? 9 rest).bind fun (slots, rest) =>
          if hl : slots.length = 9 then
            match rest with
            | count :: rest =>
              if 0 ≤ count then
                (decodeEdits? count.toNat rest).map fun edits =>
                  { seed := seed.toNat.toUInt64
                    player := { pos := ⟨px, py, pz⟩, vel := ⟨vx, vy, vz⟩, onGround, flying }
                    inventory := ⟨⟨slots.toArray, by simp [hl]⟩⟩
                    selected := ⟨selected.toNat, by omega⟩
                    edits }
              else none
            | [] => none
          else none
      else none
    else none
  | _ => none

/-- A saved game as text: one integer per line. -/
def toText (d : SaveData) : String :=
  "\n".intercalate (d.encode.map toString)

/-- Read a saved game from text. -/
def ofText? (text : String) : Option SaveData :=
  let lines : List String := (text.splitOn "\n").filter (· ≠ "")
  (lines.mapM String.toInt?).bind decode?

/--
Rebuild a session from saved data, if the data describes a sound game. The
session remembers the seed, so it can be saved again.
-/
def restore? (d : SaveData) : Option Session :=
  if hfloor : d.edits.all (fun e => e.1.y != 0 || e.2 == .bedrock) then
    Session.start? ((Terrain.world d.seed).setMany d.edits)
      (fun x z => by
        have hbase := Terrain.world_floor_get d.seed
        generalize Terrain.world d.seed = w at hbase
        have hall : ∀ e ∈ d.edits, e.1.y = 0 → e.2 = Block.bedrock := by
          intro e he hy
          have := List.all_eq_true.mp hfloor e he
          simpa [hy] using this
        clear hfloor
        generalize d.edits = edits at hall
        induction edits generalizing w with
        | nil => exact hbase x z
        | cons e es ih =>
          refine ih (w.set e.1 e.2) (fun x z => ?_) (fun e' he' => hall e' (List.mem_cons_of_mem _ he'))
          rw [World.get_set]
          split
          · next heq => exact hall e List.mem_cons_self (by rw [← heq])
          · exact hbase x z)
      d.player d.inventory d.selected (some d.seed)
      (fun sd h => by
        cases h
        rw [World.terrain_setMany]
        rfl)
  else none

end SaveData

namespace Session

/--
The data to save for a session, if its world was generated from a seed. The
seed is the session's own, which is proved to be its terrain's.
-/
def snapshot (s : Session) : Option SaveData :=
  s.seed.map fun seed =>
    { seed
      player := s.state.player
      inventory := s.state.inventory
      selected := s.state.selected
      edits := s.state.world.edits.toList }

end Session

end LeanMc
