/-!
# The fox's looks

What a fox is drawn as: a handful of coloured boxes. This is cosmetic and
unverified. Where the fox is and which way it faces come from `LeanMc.Core`.
-/

namespace LeanMc.Shell.Fox

/--
One box of the model. Its low corner and its size are in model pixels, measured
from the middle of the fox's feet as it faces north: `x` to its right, `y` up
and `z` behind it.
-/
structure Part where
  x : Float
  y : Float
  z : Float
  sx : Float
  sy : Float
  sz : Float
  rgba : UInt32

/-- Blocks per model pixel. The model is about 27 pixels from nose to tail, a little over a block. -/
def scale : Float := 0.044

def orange : UInt32 := 0xe8822cff
def cream : UInt32 := 0xf6efe2ff
def brown : UInt32 := 0x4a2c1aff
def black : UInt32 := 0x1c1612ff

/-- The fox: four legs, a body, a big head with a snout and ears, and a white-tipped tail. -/
def parts : List Part := [
  -- Legs, in dark socks.
  ⟨-3, 0, -5, 2, 3, 2, brown⟩, ⟨1, 0, -5, 2, 3, 2, brown⟩,
  ⟨-3, 0, 3, 2, 3, 2, brown⟩, ⟨1, 0, 3, 2, 3, 2, brown⟩,
  -- Body, with a pale chest.
  ⟨-3, 3, -5, 6, 5, 10, orange⟩,
  ⟨-2, 3, -5.3, 4, 3, 0.3, cream⟩,
  -- Head.
  ⟨-4, 5, -10, 8, 6, 5, orange⟩,
  -- Snout and nose.
  ⟨-2, 5, -13, 4, 2, 3, cream⟩,
  ⟨-1, 6, -13.5, 2, 1, 0.5, black⟩,
  -- Eyes.
  ⟨-3, 8, -10.2, 1, 1, 0.2, black⟩, ⟨2, 8, -10.2, 1, 1, 0.2, black⟩,
  -- Ears, with dark tips.
  ⟨-4, 11, -8, 2, 2, 1, orange⟩, ⟨2, 11, -8, 2, 2, 1, orange⟩,
  ⟨-4, 13, -8, 2, 1, 1, brown⟩, ⟨2, 13, -8, 2, 1, 1, brown⟩,
  -- Tail, with a white tip.
  ⟨-2, 4, 5, 4, 4, 5, orange⟩,
  ⟨-2, 4, 10, 4, 4, 3, cream⟩
]

end LeanMc.Shell.Fox
