/-!
# Blocks

The kinds of block the world is made of, and the few properties the rest of
the core cares about.
-/

namespace LeanMc

inductive Block where
  | air
  | bedrock
  | stone
  | dirt
  | grass
  | sand
  | log
  | leaves
  | planks
  | cobble
  deriving DecidableEq, Repr, Inhabited

namespace Block

/-- Blocks that are drawn at all. -/
def isVisible : Block → Bool
  | air => false
  | _ => true

/-- Blocks that completely hide whatever is behind them. -/
def isOpaque : Block → Bool
  | air => false
  | _ => true

/-- Blocks that stop movement. -/
def isSolid : Block → Bool
  | air => false
  | _ => true

end Block

end LeanMc
