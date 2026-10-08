import LeanMc.Core.Block

/-!
# Inventory

The blocks the player is carrying: nine slots, each empty or holding a stack of
one kind of block.

A stack's size is stored as one less than its count, in `Fin 64`, so a stack
always holds between 1 and 64 blocks. An empty or oversized stack cannot be
written down, let alone reached.
-/

namespace LeanMc

/-- Between 1 and 64 blocks of one kind. -/
structure Stack where
  block : Block
  /-- One less than the number of blocks. -/
  extra : Fin 64
  deriving DecidableEq, Repr

namespace Stack

/-- The most blocks a stack holds. -/
def limit : Nat := 64

def count (s : Stack) : Nat :=
  s.extra.val + 1

/-- The slot after one more `b` is put in it, if `b` fits: an empty slot, or a stack of `b` with room. -/
def put? : Option Stack → Block → Option Stack
  | none, b => some ⟨b, 0⟩
  | some s, b =>
    if h : s.block = b ∧ s.extra.val < 63 then some ⟨b, ⟨s.extra.val + 1, by omega⟩⟩ else none

/-- The slot after one block is taken from a stack: a smaller stack, or nothing. -/
def takeOne (s : Stack) : Option Stack :=
  if h : s.extra.val = 0 then none else some ⟨s.block, ⟨s.extra.val - 1, by omega⟩⟩

end Stack

structure Inventory where
  slots : Vector (Option Stack) 9 := Vector.replicate 9 none
  deriving DecidableEq, Repr

namespace Inventory

/-- How many of block `b` a slot holds. -/
def slotCount (b : Block) : Option Stack → Nat
  | some s => if s.block = b then s.count else 0
  | none => 0

/-- How many of block `b` the player is carrying. -/
def count (inv : Inventory) (b : Block) : Nat :=
  (inv.slots.toList.map (slotCount b)).sum

/-- Where one more `b` would go: a stack of `b` with room if there is one, else an empty slot. -/
def roomFor (inv : Inventory) (b : Block) : Option (Fin 9) :=
  match (List.finRange 9).find? fun i => inv.slots[i].isSome && (Stack.put? inv.slots[i] b).isSome with
  | some i => some i
  | none => (List.finRange 9).find? fun i => (Stack.put? inv.slots[i] b).isSome

/-- Pick up one `b`, if there is room for it. -/
def add (inv : Inventory) (b : Block) : Option Inventory :=
  match inv.roomFor b with
  | none => none
  | some i =>
    match Stack.put? inv.slots[i] b with
    | some stack => some ⟨inv.slots.set i (some stack)⟩
    | none => none

/-- Take one block out of slot `i`, if it holds any: the block, and what is left. -/
def take (inv : Inventory) (i : Fin 9) : Option (Block × Inventory) :=
  match inv.slots[i] with
  | none => none
  | some s => some (s.block, ⟨inv.slots.set i s.takeOne⟩)

/-- The stack in slot `i`, if any. -/
def stack (inv : Inventory) (i : Fin 9) : Option Stack :=
  inv.slots[i]

end Inventory

end LeanMc
