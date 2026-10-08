import Lake
open Lake DSL System

package leanmc

def raylibVersion := "5.5"
def raylibUrl := s!"https://github.com/raysan5/raylib/archive/refs/tags/{raylibVersion}.tar.gz"
def raylibSha256 := "aea98ecf5bc5c5e0b789a76de0083a21a70457050ea4cc2aec7566935f5e258e"
def raylibSrc : FilePath := "vendor" / s!"raylib-{raylibVersion}" / "src"

/-- System frameworks raylib needs on macOS. -/
def macFrameworks : Array String := #[
  "Cocoa", "IOKit", "CoreVideo", "CoreFoundation", "CoreGraphics", "OpenGL",
  "CoreAudio", "AudioToolbox"
]

/--
raylib, fetched into `vendor/` on first build and built as a dynamic library.

Lean's bundled linker cannot read the framework stubs of recent macOS SDKs, so
the frameworks are linked here by the system toolchain. The executable then
only has to link against this one ordinary dylib.
-/
target raylib pkg : Dynlib := Job.async do
  let vendorDir := pkg.dir / "vendor"
  let srcDir := pkg.dir / raylibSrc
  let staticLib := srcDir / "libraylib.a"
  let dylib := pkg.sharedLibDir / "libraylib.dylib"
  unless ← srcDir.pathExists do
    let tarball := vendorDir / s!"raylib-{raylibVersion}.tar.gz"
    IO.FS.createDirAll vendorDir
    proc { cmd := "curl", args := #["-sSfL", "-o", tarball.toString, raylibUrl] }
    let sum ← captureProc { cmd := "shasum", args := #["-a", "256", tarball.toString] }
    unless sum.startsWith raylibSha256 do
      error s!"raylib download has an unexpected checksum: {sum}"
    proc { cmd := "tar", args := #["-xzf", tarball.toString, "-C", vendorDir.toString] }
    IO.FS.removeFile tarball
  unless ← staticLib.pathExists do
    proc {
      cmd := "make"
      args := #["-C", srcDir.toString, "PLATFORM=PLATFORM_DESKTOP", "RAYLIB_LIBTYPE=STATIC"]
    }
  unless ← dylib.pathExists do
    IO.FS.createDirAll pkg.sharedLibDir
    proc {
      cmd := "cc"
      args := #["-dynamiclib", "-o", dylib.toString, "-install_name", dylib.toString,
        "-Wl,-all_load", staticLib.toString]
        ++ macFrameworks.flatMap fun f => #["-framework", f]
    }
  return { path := dylib, name := "raylib" }

/--
The C shim. It needs system headers, so it uses the system compiler rather than
Lean's. It waits for `raylib`, whose headers it includes.
-/
target shim.o pkg : FilePath := do
  (← raylib.fetch).bindM fun _ => do
    let oFile := pkg.buildDir / "ffi" / "shim.o"
    let srcJob ← inputTextFile <| pkg.dir / "ffi" / "shim.c"
    let weakArgs := #["-I", (← getLeanIncludeDir).toString, "-I", (pkg.dir / raylibSrc).toString]
    buildO oFile srcJob weakArgs #["-O2", "-fPIC"] "cc"

lean_lib LeanMc

@[default_target]
lean_exe leanmc where
  root := `Main
  moreLinkObjs := #[shim.o]
  moreLinkLibs := #[raylib]
