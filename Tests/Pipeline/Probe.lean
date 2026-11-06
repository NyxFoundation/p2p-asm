import Lean
import Libp2pAsm.Asm.Crypto.Quic.Kdf
import Libp2pAsm.Asm.Crypto.Quic.Packet
import Libp2pAsm.Asm.Quic.Wire
import Libp2pAsm.Asm.Tls.Codec
import Libp2pAsm.Rv64.Execution

/-!
ASM-core chain integration: Initial key derivation, packet unprotection,
QUIC packet/frame parsing, and TLS ClientHello decoding, driven through the
lowered RV64IM instruction sequences of each frozen leaf. Every leaf is
individually GNU/QEMU verified by its own suite; this chain runs in the Lean
machine model and checks exact registers, buffers and preserved registers.
-/

namespace Libp2pAsm.Tests.Pipeline
open Rv64

private def fail (message : String) : IO α := throw (IO.userError message)

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do fail message

private structure Output where
  addr : Nat
  bytes : Array Nat
  deriving Lean.FromJson

private structure Stage where
  name : String
  args : Array Nat
  status : Nat
  aux : Array (Array Nat)
  outputs : Array Output
  stackClear : Array Nat
  deriving Lean.FromJson

private structure Case where
  base : Nat
  stackBase : Nat
  stackSize : Nat
  initialRegs : Array Nat
  region : Array Nat
  stack : Array Nat
  stages : Array Stage
  expectRegion : Array Nat
  expectStack : Array Nat
  clientHello : Array Nat
  deriving Lean.FromJson

/-- Engineering bounds quoted per leaf; TLS uses the published Spec estimate. -/
private def bound (name : String) (chLength : Nat) : Nat :=
  match name with
  | "kdf" => 3000000
  | "open" => 3000000
  | "packet" => 300000
  | "frame" => 300000
  | "tls" => 2000000 + 200000 * (chLength + 4)
  | _ => 0

private def leaf (name : String) : Except String SAsm.Stmt :=
  match name with
  | "kdf" => Asm.Crypto.Quic.Kdf.derive .initial
  | "open" => Asm.Crypto.Quic.Packet.unprotect
  | "packet" => Asm.Quic.Wire.packetParse
  | "frame" => Asm.Quic.Wire.frameParse
  | "tls" => Asm.Tls.Codec.decode
  | _ => .error s!"unknown stage {name}"

/-- ra, sp, gp, tp and the callee-saved registers these leaves preserve. -/
private def preserved : Array Nat :=
  #[1, 2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

private def regTable : Array Reg := #[.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7,
  .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19,
  .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

private def dumpRegs (st : State) : String :=
  String.intercalate " " ((List.range 32).map fun i =>
    match regTable[i]? with
    | some r => s!"x{i}={(st.getReg r |>.toNat)}"
    | none => "")


private def regAt (index : Nat) : IO Reg :=
  match regTable[index]? with
  | some r => pure r
  | none => fail s!"register id {index} out of range"


private def byteOf (n : Nat) : UInt8 := UInt8.ofNat (n % 256)

private def u8Array (xs : Array Nat) : Array UInt8 := xs.map byteOf

private def readSpan (memory : Memory) (address size : Nat) : Except String (Array UInt8) := do
  if size == 0 then return #[]
  let found := memory.regions.find? (fun r =>
    decide (address ≥ r.base.toNat && address + size ≤ r.base.toNat + r.bytes.size))
  let region ← match found with
    | some r => .ok r
    | none => .error s!"unmapped span {address}+{size}"
  return region.bytes.extract (address - region.base.toNat) (address + size - region.base.toNat)

def main (args : List String) : IO Unit := do
  let [directory] := args | fail "usage: pipeline-probe case-directory"
  let dir : System.FilePath := directory
  let json ← match Lean.Json.parse (← IO.FS.readFile (dir / "case.json")) with
    | .ok data => pure data
    | .error e => fail s!"invalid fixture JSON: {e}"
  let .ok case := Lean.fromJson? (α := Case) json | fail "invalid fixture JSON"
  check (case.initialRegs.size == 32) "32 initial registers"
  check (case.region.size == case.expectRegion.size) "region snapshot size"
  check (case.stack.size == case.expectStack.size) "stack snapshot size"
  for stage in case.stages do
    check (stage.args.all (· < 2^64)) s!"{stage.name}: arguments fit u64"
    check (stage.aux.all (fun pair => pair.size == 2)) s!"{stage.name}: aux pairs of two"
    check (stage.stackClear.size == 2) s!"{stage.name}: stackClear pair"
  let registers : Vector Word 32 :=
    Vector.ofFn (fun (i : Fin 32) => BitVec.ofNat 64 case.initialRegs[i]!)
  let memory : Memory := { regions := #[
    { base := BitVec.ofNat 64 case.base, bytes := u8Array case.region, writable := true },
    { base := BitVec.ofNat 64 case.stackBase, bytes := u8Array case.stack,
      writable := true }] }
  check memory.valid "fixture memory is valid"
  let start : State := { pc := 0x10000, memory, regs := registers }
  let mut programs : Array (String × Program) := #[]
  for stage in case.stages do
    let source ← match leaf stage.name with
      | .ok body => .ok body
      | .error e => fail s!"{stage.name}: {e}"
    let lowered ← match source.lower with
      | .ok code => .ok code
      | .error e => fail s!"{stage.name}: lower {repr e}"
    programs := programs.push (stage.name, ⟨0x10000, lowered⟩)
  let mut state := start
  let mut total := 0
  for stage in case.stages do
    let some (_, program) := programs.find? (fun (n, _) => n == stage.name)
      | fail s!"{stage.name}: missing program"
    let mut withArgs := { state with pc := 0x10000 }
    for (item, i) in stage.args.toList.zipIdx do
      if item != 0 then
        withArgs := withArgs.setReg (← regAt (10 + i)) (BitVec.ofNat 64 item)
    let limit := bound stage.name case.clientHello.size
    let done ← match runUntil program 0x80000 limit withArgs with
      | .ok done => pure done
      | .error trap => fail s!"{stage.name}: trap {repr trap}"
    total := total + done.steps
    check (done.steps ≤ limit) s!"{stage.name}: steps {done.steps} exceed bound {limit}"
    if done.state.getReg .x10 != BitVec.ofNat 64 stage.status then
      let descriptor ← match readSpan withArgs.memory (withArgs.getReg .x10 |>.toNat) 64 with
        | .ok data => pure data
        | .error _ => pure #[]
      fail (s!"{stage.name}: status x10 = {done.state.getReg .x10 |>.toNat}, want "
        ++ s!"{stage.status} | {dumpRegs done.state} | {descriptor.toList}")
    for pair in stage.aux do
      let index := pair[0]!
      let value := pair[1]!
      let reg ← regAt index
      check (done.state.getReg reg == BitVec.ofNat 64 value)
        s!"{stage.name}: x{index} = {done.state.getReg reg |>.toNat}, want {value}"
    for output in stage.outputs do
      let actual ← match readSpan done.state.memory output.addr output.bytes.size with
        | .ok data => .ok data
        | .error e => fail s!"{stage.name}: {e}"
      let difference := (actual.zip output.bytes).findIdx?
        (fun (a, b) => a != byteOf b)
      let position := match difference.map toString with
        | some text => text
        | none => "end"
      check (actual == u8Array output.bytes)
        s!"{stage.name}: output {output.addr} differs at byte {position}"
    if 0 < stage.stackClear[1]! then
      let cleared ← match readSpan done.state.memory stage.stackClear[0]!
          stage.stackClear[1]! with
        | .ok data => .ok data
        | .error e => fail s!"{stage.name}: {e}"
      check (cleared.all (· == 0)) s!"{stage.name}: owned stack wipe"
    for index in preserved do
      let reg ← regAt index
      check (done.state.getReg reg == start.getReg reg)
        s!"{stage.name}: preserved x{index} changed"
    state := done.state
    IO.println s!"PASS {stage.name}: {done.steps} instructions (bound {limit})"
  let region ← match readSpan state.memory case.base case.region.size with
    | .ok data => .ok data
    | .error e => fail s!"final region: {e}"
  check (region == u8Array case.expectRegion) "final buffer region snapshot"
  let stack ← match readSpan state.memory case.stackBase case.stack.size with
    | .ok data => .ok data
    | .error e => fail s!"final stack: {e}"
  check (stack == u8Array case.expectStack) "final stack snapshot"
  IO.println (s!"PASS chain: {case.stages.size} stages, {total} instructions, "
    ++ "exact buffers and registers")

end Libp2pAsm.Tests.Pipeline
