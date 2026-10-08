import LeanMc.FFI

/-!
Milestone 0 spike: proves out the native boundary end to end.
A cube mesh is packed in Lean, uploaded through the shim and drawn with a
mouse-look fly camera. `--selftest <png>` renders a few frames, saves a
screenshot and exits, so the pipeline can be checked without a person.
-/

open LeanMc FFI

/-- Corners of each cube face, counter-clockwise seen from outside. Order: +x -x +y -y +z -z. -/
def faceCorners : Array (Array (UInt8 × UInt8 × UInt8)) := #[
  #[(1,0,0), (1,1,0), (1,1,1), (1,0,1)],
  #[(0,0,1), (0,1,1), (0,1,0), (0,0,0)],
  #[(0,1,0), (0,1,1), (1,1,1), (1,1,0)],
  #[(0,0,1), (0,0,0), (1,0,0), (1,0,1)],
  #[(1,0,1), (1,1,1), (0,1,1), (0,0,1)],
  #[(0,0,0), (0,1,0), (1,1,0), (1,0,0)]
]

def faceShade : Array UInt8 := #[200, 200, 255, 120, 170, 170]

def pushVertex (out : ByteArray) (p : UInt8 × UInt8 × UInt8) (shade normal : UInt8) : ByteArray :=
  out.push p.1 |>.push p.2.1 |>.push p.2.2 |>.push 0 |>.push 0 |>.push shade |>.push normal |>.push 0

def cubeMesh : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for n in [0:6] do
    let c := faceCorners[n]!
    for i in [0, 1, 2, 0, 2, 3] do
      out := pushVertex out c[i]! faceShade[n]! n.toUInt8
  return out

structure Spike where
  x : Float := 0.5
  y : Float := 1.5
  z : Float := 4.0
  yaw : Float := 0.0
  pitch : Float := -0.25
  captured : Bool := false

def Spike.dir (s : Spike) : Float × Float × Float :=
  (s.yaw.sin * s.pitch.cos, s.pitch.sin, -(s.yaw.cos * s.pitch.cos))

def render (s : Spike) (mesh : UInt32) (frame : Nat) : IO Unit := do
  beginFrame 0x87b5ffff
  let (dx, dy, dz) := s.dir
  begin3D s.x s.y s.z (s.x + dx) (s.y + dy) (s.z + dz) 70.0
  for i in [0:5] do
    drawMesh mesh (i.toFloat * 2.0 - 4.0) 0.0 0.0
  end3D
  let w ← screenWidth
  let h ← screenHeight
  drawRect (w / 2 - 1) (h / 2 - 8) 2 16 0xffffffff
  drawRect (w / 2 - 8) (h / 2 - 1) 16 2 0xffffffff
  drawText s!"lean-mc spike  frame {frame}" 10 10 20 0xffffffff
  drawText "click: capture mouse   WASD/space/shift: fly   esc: release" 10 34 16 0xffffffff

def update (s : Spike) : IO Spike := do
  let mut s := s
  if (← mousePressed Mouse.left) && !s.captured then
    setCursorCaptured true
    s := { s with captured := true }
  if (← keyPressed Key.escape) && s.captured then
    setCursorCaptured false
    s := { s with captured := false }
  if s.captured then
    let yaw := s.yaw + (← mouseDx) * 0.003
    let pitch := s.pitch - (← mouseDy) * 0.003
    s := { s with yaw, pitch := max (-1.55) (min 1.55 pitch) }
  let step := (← frameTime) * 5.0
  let (fx, fz) := (s.yaw.sin, -s.yaw.cos)
  if ← keyDown Key.w then s := { s with x := s.x + fx * step, z := s.z + fz * step }
  if ← keyDown Key.s then s := { s with x := s.x - fx * step, z := s.z - fz * step }
  if ← keyDown Key.d then s := { s with x := s.x - fz * step, z := s.z + fx * step }
  if ← keyDown Key.a then s := { s with x := s.x + fz * step, z := s.z - fx * step }
  if ← keyDown Key.space then s := { s with y := s.y + step }
  if ← keyDown Key.leftShift then s := { s with y := s.y - step }
  return s

partial def loop (s : Spike) (mesh : UInt32) (frame : Nat) (selftest : Option String) : IO Unit := do
  if ← windowShouldClose then return
  let s ← update s
  render s mesh frame
  if let some path := selftest then
    if frame == 5 then
      takeScreenshot path
      endFrame
      return
  endFrame
  loop s mesh (frame + 1) selftest

/--
Program entry point. It is exported rather than named `main` so that the shim's
C `main` can call it on the process's main thread; see `ffi/shim.c`.
-/
@[export lmc_main]
def lmcMain (args : List String) : IO UInt32 := do
  let selftest := match args with
    | ["--selftest", path] => some path
    | _ => none
  initWindow 1280 720 "lean-mc"
  let mesh ← uploadMesh cubeMesh
  loop {} mesh 0 selftest
  unloadMesh mesh
  closeWindow
  return 0
