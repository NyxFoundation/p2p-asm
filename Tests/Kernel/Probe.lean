import Tests.Kernel.Support
import Libp2pAsm.Asm.Kernel.Limits
import Libp2pAsm.Spec.Kernel.Limits
import Libp2pAsm.Asm.Kernel.Registry
import Libp2pAsm.Spec.Kernel.Registry
import Libp2pAsm.Asm.Kernel.Queue
import Libp2pAsm.Spec.Kernel.Queue
import Libp2pAsm.Asm.Kernel.Requests
import Libp2pAsm.Spec.Kernel.Requests
import Libp2pAsm.Asm.Kernel.Layout
import Libp2pAsm.Spec.Kernel.Layout
import Libp2pAsm.Asm.Kernel.Admission
import Libp2pAsm.Spec.Kernel.Admission
import Libp2pAsm.Asm.Kernel.Connections
import Libp2pAsm.Spec.Kernel.Connections
import Libp2pAsm.Asm.Kernel.Integration
import Libp2pAsm.Spec.Kernel.Integration

namespace Libp2pAsm.Tests.Kernel
open Rv64

def program (kind : String) : Except String SAsm.Stmt :=
  if kind == "copy" then Asm.Kernel.copyRegistered else
  if kind == "kernel-quantum" then .ok Asm.Kernel.kernelQuantum else
  if kind == "resolve" then Asm.Kernel.resolveRegistered else
  if kind == "owned-issue" then Asm.Kernel.issueOwned else
  if kind == "owned-reap" then Asm.Kernel.reapOwned else
  if kind.startsWith "connection-" then
    let op := (kind.drop 11).toString.toNat!
    .ok (if op == 0 then Asm.Kernel.connectionAcquire else if op == 3 then Asm.Kernel.connectionCleanup else Asm.Kernel.connectionRelease (op == 1))
  else if kind == "admit" then .ok Asm.Kernel.admitDatagram else
  if kind == "charge" then .ok Asm.Kernel.charge else
  if kind == "quantum" then .ok Asm.Kernel.nextQuantum else
  if kind == "init-begin" then .ok Asm.Kernel.initBegin else
  if kind == "init-resume" then .ok Asm.Kernel.initResume else
  if kind.startsWith "queue-" then
    let op := (kind.drop 6).toString.toNat!
    .ok (match op with
      | 0 => Asm.Kernel.queueEnqueue false | 1 => Asm.Kernel.queueDequeue
      | 2 => Asm.Kernel.queueReserve false | 3 => Asm.Kernel.queueReserve true
      | _ => Asm.Kernel.queueEnqueue true)
  else if kind.startsWith "request-" then
    let op := (kind.drop 8).toString.toNat!
    .ok (match op with
      | 0 => Asm.Kernel.requestIssue | 1 => Asm.Kernel.requestComplete
      | 2 => Asm.Kernel.requestReap | 3 => Asm.Kernel.requestCleanup
      | 4 => Asm.Kernel.requestStop false | 5 => Asm.Kernel.requestStop true | 6 => Asm.Kernel.requestNext | _ => Asm.Kernel.requestExpireNext)
  else if kind.startsWith "registry-" then
    let op := (kind.drop 9).toString.toNat!
    if op == 0 then .ok Asm.Kernel.registryBegin else
    if op == 1 then .ok Asm.Kernel.registryResume else
    if op == 9 then .ok Asm.Kernel.registryEndStep else
    .ok (Asm.Kernel.registryMutation op)
  else if kind == "limits" || kind == "abi" then .ok Asm.Kernel.validateLimits else
  if kind == "limits-export" then .ok Asm.Kernel.exportLimits else .error "unknown kernel leaf"

def checkSpec (kind : String) (f : Fixture) : IO Unit := do
  if !f.entered then return
  if kind == "kernel-quantum" then
    let a := Spec.Kernel.unpack ((f.regions[0]!.extract 8 (8+f.args[1]!)).map Nat.toUInt8)
    let r := Spec.Kernel.kernelQuantum a
    let want := Spec.Kernel.unpack ((f.after[0]!.extract 8 (8+f.args[1]!)).map Nat.toUInt8)
    check s!"{f.label}: kernel quantum Spec" (r.status == f.status && r.first == f.first &&
      r.second == f.second && r.state == want)
  if kind == "copy" then
    let a := Spec.Kernel.unpack ((f.regions[0]!.extract 8 (8+f.args[1]!)).map Nat.toUInt8)
    let v := Spec.Kernel.unpack ((f.regions[1]!.extract 9 (9+f.args[3]!)).map Nat.toUInt8)
    let r := Spec.Kernel.resolveRegistered a v 0
    let e := if r.status != 0 then r.status else if r.second > f.args[5]! then 11 else if r.second > 65536 then 19 else 0
    check s!"{f.label}: copy Spec" (e == f.status && f.first == (if e == 0 then r.second else 0))
    if e == 0 then
      let bytes := f.regions[3]!.extract (r.first-base 3) (r.first-base 3+r.second)
      check s!"{f.label}: copied bytes" (bytes == f.after[2]!.extract 8 (8+r.second))
  if kind.startsWith "connection-" || kind.startsWith "owned-" || kind == "resolve" then
    let a := Spec.Kernel.unpack ((f.regions[0]!.extract 8 (8+f.args[1]!)).map Nat.toUInt8)
    let bytes := ((f.regions[1]!.extract 9 (9+f.args[3]!)).map Nat.toUInt8).toList
    let v := Spec.Kernel.unpack bytes.toArray
    let (r,out) := if kind.startsWith "owned-" then Spec.Kernel.owned a bytes (kind == "owned-reap") else
      if kind == "resolve" then (Spec.Kernel.resolveRegistered a v f.args[6]!,[]) else
        if kind == "connection-3" then Spec.Kernel.connectionCleanup a f.args[6]! else
          (Spec.Kernel.connections a v (kind.drop 11).toString.toNat!,[])
    let want := Spec.Kernel.unpack ((f.after[0]!.extract 8 (8+f.args[1]!)).map Nat.toUInt8)
    check s!"{f.label}: integrated resource Spec" (r.status == f.status && r.first == f.first &&
      r.second == f.second && r.state == want)
    check s!"{f.label}: integrated output"
      (out == ((f.after[2]!.extract 8 (8+out.length)).map Nat.toUInt8).toList)
  if kind == "admit" || kind == "charge" || kind == "quantum" then
    let a := Spec.Kernel.unpack ((f.regions[0]!.extract 8 (8+f.args[1]!)).map Nat.toUInt8)
    let v := Spec.Kernel.unpack ((f.regions[1]!.extract 9 (9+f.args[3]!)).map Nat.toUInt8)
    let r := if kind == "admit" then Spec.Kernel.admission a v else
      if kind == "charge" then Spec.Kernel.charge a v else Spec.Kernel.nextQuantum a
    let want := Spec.Kernel.unpack ((f.after[0]!.extract 8 (8+f.args[1]!)).map Nat.toUInt8)
    check s!"{f.label}: admission/ledger Spec" (r.status == f.status && r.first == f.first &&
      r.second == f.second && r.state == want)
  if kind.startsWith "init-" then
    let off := f.args[0]!-base 0
    let a := Spec.Kernel.unpack ((f.regions[0]!.extract off (off+f.args[1]!)).map Nat.toUInt8)
    let bs := (f.regions[1]!.extract 9 (9+f.args[3]!)).map Nat.toUInt8
    let r := if kind == "init-begin" then Spec.Kernel.initBegin a bs f.args[0]! f.args[1]! f.args[6]! f.args[7]!
      else Spec.Kernel.initResume a f.args[0]!
    let want := Spec.Kernel.unpack ((f.after[0]!.extract off (off+f.args[1]!)).map Nat.toUInt8)
    check s!"{f.label}: initialization Spec" (r.status == f.status && r.first == f.first &&
      r.second == f.second && r.state == want)
  if kind.startsWith "queue-" || kind.startsWith "request-" then
    let a := Spec.Kernel.unpack ((f.regions[0]!.extract 8 (8+f.args[1]!)).map Nat.toUInt8)
    let v := ((f.regions[1]!.extract 9 (9+f.args[3]!)).map Nat.toUInt8).toList
    let (r,out) := if kind.startsWith "queue-" then
      Spec.Kernel.queue a v (kind.drop 6).toString.toNat! f.args[6]!
      else Spec.Kernel.requests a v (kind.drop 8).toString.toNat! f.args[6]!
    let want := Spec.Kernel.unpack ((f.after[0]!.extract 8 (8+f.args[1]!)).map Nat.toUInt8)
    check s!"{f.label}: resource Spec {repr r}"
      (r.status == f.status && r.first == f.first && r.second == f.second && r.state == want)
    check s!"{f.label}: resource output"
      (out == ((f.after[2]!.extract 8 (8+out.length)).map Nat.toUInt8).toList)
  if kind.startsWith "registry-" then
    let a := Spec.Kernel.unpack ((f.regions[0]!.extract 8 (8+f.args[1]!)).map Nat.toUInt8)
    let v := Spec.Kernel.unpack ((f.regions[1]!.extract 9 (9+f.args[3]!)).map Nat.toUInt8)
    let op := (kind.drop 9).toString.toNat!
    let r := Spec.Kernel.registry a v op
    let want := Spec.Kernel.unpack ((f.after[0]!.extract 8 (8+f.args[1]!)).map Nat.toUInt8)
    check s!"{f.label}: registry Spec" (r.status == f.status && r.first == f.first &&
      r.second == f.second && r.state == want)
  if kind == "limits" || kind == "limits-export" then
    let bs := (f.regions[1]!.extract 9 (9+f.args[3]!)).map Nat.toUInt8
    match Spec.Kernel.validateRaw bs with
    | .error e => check s!"{f.label}: Spec error {e}" (e == f.status)
    | .ok l =>
      check s!"{f.label}: Spec reserved bytes"
        (f.status == 0 && f.first == (if kind == "limits" then l.reservedBytes else 488))

def run (kind : String) (dir : System.FilePath) : IO Unit := do
  let .ok stmt := program kind | throw (IO.userError "unknown leaf")
  let .ok code := stmt.lower | throw (IO.userError "lower failed")
  let .ok bytes := encodeProgram code | throw (IO.userError "encode failed")
  IO.FS.writeFile (dir/"protocol.S") (Codegen.assembly code)
  IO.FS.writeBinFile (dir/"encoded.bin") bytes
  let .ok json := Lean.Json.parse (← IO.FS.readFile (dir/"cases.json"))
    | throw (IO.userError "invalid JSON")
  let fs ← match Lean.fromJson? (α := Array Fixture) json with
    | .ok fs => pure fs | .error e => throw (IO.userError e)
  let mut measurements := s!"static_instructions={code.size}\n"
  for idx in List.range fs.size do
    let f := fs[idx]!
    checkSpec kind f
    let start := initial f
    let want := expected f start
    check "program mapping" ((LeanAsm.Rv64.Image.mk (0x10000 : Word) code).valid start.memory)
    let done ← match checkedLoop ⟨0x10000,code⟩ f 16777216 start 0 with
      | .ok d => pure d | .error e => throw (IO.userError s!"{f.label}: {e}")
    IO.FS.writeBinFile (dir/s!"case-{idx}.before.bin") (snapshot start)
    IO.FS.writeBinFile (dir/s!"case-{idx}.after.bin") (snapshot done.state)
    IO.FS.writeBinFile (dir/s!"case-{idx}.expected.bin") (snapshot want)
    check s!"{f.label}: full snapshot status={done.state.getReg .x10 |>.toNat}"
      (snapshot done.state == snapshot want)
    measurements := measurements ++ s!"{idx} {f.label} {done.steps}\n"
  IO.FS.writeFile (dir/"measurements.txt") measurements
  IO.println s!"PASS {kind}: {fs.size} Spec/instructions/full snapshot/footprint cases"

def main (args : List String) : IO Unit := do
  match args with
  | [kind,dir] => run kind dir
  | _ => throw (IO.userError "usage: kernel-probe kind directory")
end Libp2pAsm.Tests.Kernel
