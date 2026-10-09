import PropTest.Shrink
import Basalt.IO
import LeanMc.Shell.Game

/-!
# The shim against its model

`LeanMc.Gpu` says what the native shim's mesh table should do, and the render
planner is proved correct against that description. These tests check the
description against the real thing: random command sequences are sent to the
shim through the game's own interpreter, and its state is read back and
compared with the model's.

This needs a window, for the graphics context. Run with `lake exe native`.
-/

open LeanMc PropTest LeanMc.FFI

/-- The twelve numbers the shim should report for a vertex: position, uv, normal, colour. -/
def expectedVertex (v : GpuVertex) : List Float :=
  let normal : List Float :=
    match v.normal with
    | 0 => [1, 0, 0] | 1 => [-1, 0, 0] | 2 => [0, 1, 0] | 3 => [0, -1, 0] | 4 => [0, 0, 1]
    | _ => [0, 0, -1]
  [v.x.toFloat, v.y.toFloat, v.z.toFloat, v.u.toFloat / 16, v.v.toFloat / 16] ++ normal
    ++ [v.shade.toFloat, v.shade.toFloat, v.shade.toFloat, 255]

def expectedMesh (vertices : ByteArray) : List Float :=
  (Gpu.decode vertices).flatMap expectedVertex

def sameFloats (a b : List Float) : Bool :=
  a.length == b.length && (a.zip b).all fun (x, y) => x == y

def showCmd : GpuCmd → String
  | .upload slot v => s!"upload {slot} ({v.size} bytes: {v.data.toList.take 24}…)"
  | .unload slot => s!"unload {slot}"
  | .beginScene => "beginScene"
  | .draw slot offset => s!"draw {slot} at {offset.x} {offset.y} {offset.z}"

def showCmds (cmds : List GpuCmd) : String :=
  s!"{cmds.length} commands: {cmds.map showCmd}"

/-- Slots worth reading back: the ones the generator favours, and the edges of the table. -/
def watched : List Nat := [0, 1, 2, 3, 4, 5, 6, 16383, 16384, 16385, 70000]

/-- Does the shim read these bytes the way the model says? -/
def decodeFault (vertices : ByteArray) : IO (Option String) := do
  let got := (← debugDecode vertices).toList
  let want := expectedMesh vertices
  if sameFloats got want then return none
  return some s!"shim read {got.length / 12} vertices as {got}, model says {want}"

/--
Send commands to the shim and to a model, then compare everything that can be
read back: the fault flag, each watched slot, and the scene.
-/
def storeFault (exec : Gpu → GpuCmd → Gpu) (cmds : List GpuCmd) : IO (Option String) := do
  debugReset
  cmds.forM Shell.Game.send
  let model := cmds.foldl exec {}
  if (← debugFault) != model.fault then
    return some s!"fault flag: shim {← debugFault}, model {model.fault}"
  for slot in watched do
    let want := model.meshes[slot]?
    if (← debugMeshLive slot.toUInt32) != want.isSome then
      return some s!"slot {slot}: shim live {← debugMeshLive slot.toUInt32}, model {want.isSome}"
    let got := (← debugMesh slot.toUInt32).toList
    unless sameFloats got ((want.map expectedMesh).getD []) do
      return some s!"slot {slot} holds different vertices from the model"
  let scene := (← debugScene).toList
  let want := model.scene.flatMap fun (slot, o) =>
    [slot.toFloat, Float.ofInt o.x / 65536.0, Float.ofInt o.y / 65536.0, Float.ofInt o.z / 65536.0]
  unless sameFloats scene want do
    return some s!"scene: shim drew {scene.length / 4} meshes {scene}, model {want}"
  return none

/-- A wrong model, which forgets to empty slots: the tests must notice. -/
def forgetfulExec (g : Gpu) : GpuCmd → Gpu
  | .unload _ => g
  | cmd => g.exec cmd

def parseArgs (runs seed : Nat) : List String → Nat × Nat
  | "--runs" :: n :: rest => parseArgs (n.toNat?.getD runs) seed rest
  | "--seed" :: n :: rest => parseArgs runs (n.toNat?.getD seed) rest
  | _ :: rest => parseArgs runs seed rest
  | [] => (runs, seed)

@[export lmc_native_main]
def nativeMain (args : List String) : IO UInt32 := do
  let (runs, seed) := parseArgs 300 (← IO.monoNanosNow) args
  ioGen.set (SplitMix.ofSeed seed.toUInt64)
  IO.println s!"shim against model: {runs} runs each, seed {seed}"
  initWindow 320 240 "lean-mc shim tests"
  let mut ok := true

  ok := (← holds "the shim reads vertices the way the model says" (runs * 3)
    genDecodeBytes shrinkMesh
    (fun v => s!"{v.size} bytes: {v.data.toList}") decodeFault) && ok

  ok := (← holds "the shim's mesh table and scene match the model after any commands" runs
    genGpuCmds (shrinkList shrinkGpuCmd) showCmds (storeFault Gpu.exec)) && ok

  ok := (← refutes "self-check: a model that forgets to unload is caught" runs
    genGpuCmds (shrinkList shrinkGpuCmd) List.length 2 showCmds
    (storeFault forgetfulExec)) && ok

  debugReset
  closeWindow
  return if ok then 0 else 1
