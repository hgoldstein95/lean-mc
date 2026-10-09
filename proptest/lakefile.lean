import Lake
open Lake DSL System

/-!
Property-based tests for lean-mc, built on basalt.

This is a separate package so that the game itself does not depend on Mathlib,
which basalt needs. Build the game first (`lake build` in the parent), then
here run `lake exe cache get` once, `lake test` for the pure properties,
`lake exe native` for the tests that compare the real shim with its model, and
`lake build` to check the proofs that the generators are correct.
-/

package proptest

require leanmc from ".."

require basalt from git "https://github.com/hgoldstein95/basalt" @ "08f06f180c8517f9429fbd9ce5ac0a7e5c51dd21"

lean_lib PropTest

/--
Proofs that the generators produce exactly what `PropTest.Spec` says. These
import all of basalt, and with it Mathlib, so nothing the test executables
link may import them.
-/
@[default_target]
lean_lib PropTestProofs

@[test_driver]
lean_exe props where
  root := `Props

/-! ## The shim, for the tests that compare it with its model -/

def gameDir (pkg : Package) : FilePath := pkg.dir / ".."

target shim.o pkg : FilePath := do
  let oFile := pkg.buildDir / "ffi" / "shim.o"
  let srcJob ← inputTextFile <| gameDir pkg / "ffi" / "shim.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString,
    "-I", (gameDir pkg / "vendor" / "raylib-5.5" / "src").toString]
  buildO oFile srcJob weakArgs #["-O2", "-fPIC"] "cc"

/-- The entry point that runs the tests on the main thread, as windows require. -/
target entry.o pkg : FilePath := do
  let oFile := pkg.buildDir / "ffi" / "entry.o"
  let srcJob ← inputTextFile <| gameDir pkg / "ffi" / "entry.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs
    #["-O2", "-fPIC", "-DLMC_INIT=initialize_proptest_Native", "-DLMC_ENTRY=lmc_native_main"] "cc"

/-- raylib as the game built it. -/
target raylib pkg : Dynlib := Job.async do
  let dylib := gameDir pkg / ".lake" / "build" / "lib" / "libraylib.dylib"
  unless ← dylib.pathExists do
    error "raylib is not built yet: run `lake build` in the parent directory first"
  return { path := dylib, name := "raylib" }

lean_exe native where
  root := `Native
  moreLinkObjs := #[shim.o, entry.o]
  moreLinkLibs := #[raylib]
