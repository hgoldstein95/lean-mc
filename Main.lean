import LeanMc.Shell.Game

/--
Program entry point. It is exported rather than named `main` so that the shim's
C `main` can call it on the process's main thread; see `ffi/shim.c`.
-/
@[export lmc_main]
def lmcMain (args : List String) : IO UInt32 :=
  LeanMc.Shell.run args
