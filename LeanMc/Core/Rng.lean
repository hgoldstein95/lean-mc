import LeanMc.Core.Terrain

/-!
# Random numbers

The game's randomness is a value like any other: the state of a generator, kept
in the game state. Drawing a number gives the number and the generator to draw
the next one from, so a tick that uses randomness is still a function of the
state it starts in.

The generator is SplitMix64.
-/

namespace LeanMc

/-- The state of the random number generator. -/
structure Rng where
  state : UInt64
  deriving DecidableEq, Repr, Inhabited

namespace Rng

/-- The generator a world generated from `seed` starts with. -/
def ofSeed (seed : UInt64) : Rng :=
  ⟨seed⟩

/--
Draw a 64-bit number, together with the generator to draw the next one from.

This is `opaque`: the proofs can see that it is a function, and nothing about
which numbers it gives. No theorem should depend on that, and hiding it also
keeps Lean from trying to work the numbers out, which it cannot do for a state
it does not know.
-/
opaque next (r : Rng) : UInt64 × Rng :=
  let state := r.state + 0x9e3779b97f4a7c15
  (Terrain.mix state, ⟨state⟩)

end Rng

end LeanMc
