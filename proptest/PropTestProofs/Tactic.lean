import Basalt

/-!
# Small tactics for the generator proofs

Each law of a generator is one `walk` over its definition; what is left is
arithmetic. These close the arithmetic that keeps coming up.
-/

/--
Close the goal a termination proof leaves for a generator with no recursion:
`1 ≤ w / w`, where `w` is the total weight of a `frequency`, or `1 ≤ 1`.
-/
macro "mass_arith" : tactic =>
  `(tactic| first
    | (simp; done)
    | (norm_num; done)
    | (norm_num; exact (ENNReal.div_self (by norm_num) (by norm_num)).ge))

/--
Close a goal a soundness walk leaves on a path that drew from a literal list:
with the drawn value and its membership reverted, the goal is a check of each
element of the list.
-/
macro "by_elements" : tactic =>
  `(tactic| (rename_i v hv; revert v; decide))
