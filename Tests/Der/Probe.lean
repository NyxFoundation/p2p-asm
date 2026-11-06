import Libp2pAsm.Spec.Codec.Der
import Libp2pAsm.Asm.Codec.Der
import Tests.HashCrypto.Support

namespace Libp2pAsm.Tests.Der.Native
open Rv64
open AsmCrypto (check snapshot)
open HashCrypto (Case loadCase replaced)
open Spec.Codec.Der

private def span (ptr size : Nat) : Bool := size == 0 || ptr + size ≤ 2^64

private def decodeResult (c : Case) : Nat × List Nat :=
  let ptr := (c.start.getReg .x10).toNat
  let size := (c.start.getReg .x11).toNat
  if !span ptr size then (4, []) else
  match Spec.Codec.Der.decode c.a.toList with
  | .error e => (e.code, [])
  | .ok d => (0, [d.tag.toNat, d.header, d.length, d.consumed])

private def encodeResult (c : Case) : Nat × Array UInt8 :=
  match Spec.Codec.Der.encodeHeader (c.start.getReg .x10).toNat
      (c.start.getReg .x11).toNat with
  | .error e => (e.code, #[])
  | .ok bytes =>
    if (c.start.getReg .x13).toNat < bytes.length then (5, #[])
    else if !span (c.start.getReg .x12).toNat bytes.length then (4, #[])
    else (0, bytes.toArray)

private def expected (kind : String) (c : Case) : Nat × State :=
  let (status, outputs, bytes) := if kind == "decode" then
      let (s, fields) := decodeResult c
      (s, fields, #[])
    else
      let (s, bytes) := encodeResult c
      (s, [bytes.size], bytes)
  let regions := c.start.memory.regions.mapIdx fun i r =>
    if i == 2 && status == 0 && kind == "encode" then
      { r with bytes := replaced r.bytes 9 bytes } else r
  let cleared := Asm.Crypto.Sha2.cleared.foldl (fun s r => s.setReg r 0) c.start
  let regs : List Reg := [.x11, .x12, .x13, .x14]
  let result := (regs.zip outputs).foldl
    (fun s (r, v) => s.setReg r (BitVec.ofNat 64 v))
    (cleared.setReg .x10 (BitVec.ofNat 64 status))
  (status, { result with pc := 0x80000, memory := ⟨regions⟩ })

private def permitted (kind : String) (c : Case) (e : AsmCrypto.Event) : Bool :=
  match e.access with
  | none => true
  | some (write, width, addr) =>
    let r := if kind == "decode" then Reg.x10 else Reg.x12
    let ptr := (c.start.getReg r).toNat
    width == 1 && write == (kind == "encode") &&
      ptr ≤ addr.toNat && addr.toNat + width ≤ ptr + c.field 1

private def runCase (kind : String) (dir : System.FilePath)
    (code : Array Instr) (i : Nat) : IO Unit := do
  let c ← loadCase dir i
  check "fixture input length matches represented bytes or is an early range error"
    (kind != "decode" || (c.start.getReg .x11).toNat == c.a.size ||
      !span (c.start.getReg .x10).toNat (c.start.getReg .x11).toNat)
  let (status, want) := expected kind c
  check "independent Python and Spec statuses agree" (status == c.field 0)
  let p : Program := ⟨0x10000, code⟩
  let .ok done := runUntil p 0x80000 512 c.start
    | throw (IO.userError "DER routine trapped or exceeded budget")
  check "all registers, input, output, guards and unused memory match Spec"
    (snapshot done.state == snapshot want && done.state.pc == want.pc)
  let .ok events := AsmCrypto.trace p done.steps c.start
    | throw (IO.userError "DER trace failed")
  check "no payload/guard read, out-of-bounds store or access before metadata rejection"
    (events.all (permitted kind c))
  IO.FS.writeBinFile (dir / s!"case-{i}" / "after.bin") (snapshot done.state)
  IO.println s!"PASS {kind} case {i}: {done.steps} instructions"

def run (kind : String) (dir : System.FilePath) : IO Unit := do
  let body ← match kind with
    | "decode" => pure Asm.Codec.Der.decode
    | "encode" => pure Asm.Codec.Der.encodeHeader
    | _ => throw (IO.userError "unknown DER operation")
  let .ok code := body.lower | throw (IO.userError "DER lowering failed")
  let .ok binary := encodeProgram code | throw (IO.userError "DER encoding failed")
  IO.FS.writeFile (dir / "protocol.S") (Codegen.assembly code)
  IO.FS.writeBinFile (dir / "encoded.bin") binary
  let countText ← IO.FS.readFile (dir / "count.txt")
  let some count := countText.trimAscii.toString.toNat?
    | throw (IO.userError "invalid fixture count")
  check "bounded nonempty fixture set" (0 < count && count < 10000)
  for i in List.range count do runCase kind dir code i

end Libp2pAsm.Tests.Der.Native

def main (args : List String) : IO Unit := do
  match args with
  | [kind, dir] => Libp2pAsm.Tests.Der.Native.run kind dir
  | _ => throw (IO.userError "usage: DER-Probe encode|decode artifact-directory")
