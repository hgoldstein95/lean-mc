import Lake
open Lake DSL System

/-!
Property-based tests for lean-mc, built on basalt.

This is a separate package so that the game itself does not depend on Mathlib,
which basalt needs. Build the game first (`lake build` in the parent), then
run `lake exe cache get` and `lake test` here.
-/

package proptest

require leanmc from ".."

require basalt from git "https://github.com/hgoldstein95/basalt" @ "08f06f180c8517f9429fbd9ce5ac0a7e5c51dd21"

lean_lib PropTest

@[test_driver]
lean_exe props where
  root := `Props
