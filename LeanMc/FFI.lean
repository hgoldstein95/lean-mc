/-!
# Native bindings

Lean declarations for `ffi/shim.c`. This module and the shim behind it are the
project's trusted, unverified boundary: nothing here is modelled, so nothing in
`LeanMc.Core` may depend on it.
-/

namespace LeanMc.FFI

/-! ## Window and frame -/

@[extern "lmc_init_window"]
opaque initWindow (width height : UInt32) (title : @& String) : IO Unit

@[extern "lmc_close_window"]
opaque closeWindow : IO Unit

@[extern "lmc_window_should_close"]
opaque windowShouldClose : IO Bool

@[extern "lmc_screen_width"]
opaque screenWidth : IO UInt32

@[extern "lmc_screen_height"]
opaque screenHeight : IO UInt32

/-- Seconds taken by the previous frame. -/
@[extern "lmc_frame_time"]
opaque frameTime : IO Float

/-- Start a frame, clearing to the `0xRRGGBBAA` colour. -/
@[extern "lmc_begin_frame"]
opaque beginFrame (rgba : UInt32) : IO Unit

@[extern "lmc_end_frame"]
opaque endFrame : IO Unit

/-- Enter 3D mode with a perspective camera at `p` looking at `t`. -/
@[extern "lmc_begin_3d"]
opaque begin3D (px py pz tx ty tz fovy : Float) : IO Unit

@[extern "lmc_end_3d"]
opaque end3D : IO Unit

/-- Write the current framebuffer to an image file. -/
@[extern "lmc_take_screenshot"]
opaque takeScreenshot (path : @& String) : IO Unit

/-! ## Input -/

@[extern "lmc_key_down"]
opaque keyDown (key : UInt32) : IO Bool

@[extern "lmc_key_pressed"]
opaque keyPressed (key : UInt32) : IO Bool

@[extern "lmc_mouse_down"]
opaque mouseDown (button : UInt32) : IO Bool

@[extern "lmc_mouse_pressed"]
opaque mousePressed (button : UInt32) : IO Bool

@[extern "lmc_mouse_dx"]
opaque mouseDx : IO Float

@[extern "lmc_mouse_dy"]
opaque mouseDy : IO Float

@[extern "lmc_mouse_wheel"]
opaque mouseWheel : IO Float

@[extern "lmc_set_cursor_captured"]
opaque setCursorCaptured (captured : Bool) : IO Unit

/-! raylib key and mouse-button codes used by the game. -/

namespace Key
def space : UInt32 := 32
def zero : UInt32 := 48
def a : UInt32 := 65
def d : UInt32 := 68
def e : UInt32 := 69
def f : UInt32 := 70
def q : UInt32 := 81
def s : UInt32 := 83
def w : UInt32 := 87
def escape : UInt32 := 256
def f3 : UInt32 := 292
def leftShift : UInt32 := 340
def leftControl : UInt32 := 341
end Key

namespace Mouse
def left : UInt32 := 0
def right : UInt32 := 1
end Mouse

/-! ## Meshes -/

/-- Size of one packed vertex; see the layout comment in `ffi/shim.c`. -/
def vertexBytes : Nat := 8

/--
Upload packed, non-indexed triangle vertices and return a mesh handle.
Handle `0` means "no mesh" and is returned for empty input.
-/
@[extern "lmc_upload_mesh"]
opaque uploadMesh (vertices : @& ByteArray) : IO UInt32

/-- Draw a mesh translated by `(tx, ty, tz)`. -/
@[extern "lmc_draw_mesh"]
opaque drawMesh (mesh : UInt32) (tx ty tz : Float) : IO Unit

@[extern "lmc_unload_mesh"]
opaque unloadMesh (mesh : UInt32) : IO Unit

/-- Replace the block texture atlas with a `width × height` RGBA8 image. -/
@[extern "lmc_set_atlas"]
opaque setAtlas (width height : UInt32) (rgba : @& ByteArray) : IO Unit

/-! ## 2D overlay -/

@[extern "lmc_draw_text"]
opaque drawText (text : @& String) (x y size rgba : UInt32) : IO Unit

@[extern "lmc_draw_rect"]
opaque drawRect (x y w h rgba : UInt32) : IO Unit

end LeanMc.FFI
