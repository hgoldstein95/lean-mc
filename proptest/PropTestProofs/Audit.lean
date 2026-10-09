import LeanMc.Proofs.Audit
import PropTestProofs.Coverage
import PropTestProofs.Shrink

/-!
# Axiom audit of the generator proofs

Every theorem about the generators, checked to rest on nothing but Lean's
three standard axioms, by the same sweep the game's own proofs use. Building
this module is the check, and it fails if a proof module in this directory is
not imported here.
-/

#assert_all_standard_axioms PropTestProofs "PropTestProofs"
