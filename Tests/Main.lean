import Libp2pAsm.Rv64.Execution
import Libp2pAsm.Rv64.Encoding
import Tests.Codec
import Tests.Der
import Tests.Identity
import Tests.CertificateTime
import Tests.CertificateAlgorithms
import Tests.Certificate
import Tests.AsmCodec
import Tests.Buffer
import Tests.Crypto
import Tests.Machine
import Tests.Limits
import Tests.Clock
import Tests.ClockAsm

open Libp2pAsm.Rv64

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL: {name}")
  IO.println s!"PASS: {name}"

private def memory : Memory :=
  { regions := #[{ base := 0x20000, bytes := #[1, 2, 3, 4, 5, 6, 7, 8], writable := true }] }

private def initial : State :=
  { pc := 0x10000, memory := memory }

private def arithmetic : Program :=
  { base := 0x10000, code := #[.ADDI .x10 .x0 40, .ADDI .x10 .x10 2, .JALR .x0 .x1 0] }

private def testRegisters : IO Unit := do
  check "should keep x0 zero when written" ((initial.setReg .x0 99).getReg .x0 == 0)
  check "should preserve other registers when written"
    (((initial.setReg .x10 42).setReg .x11 7).getReg .x10 == 42)

private def testExecution : IO Unit := do
  let result := runUntil arithmetic 0 3 initial
  check "should return 42 when the generated arithmetic program runs"
    (match result with | .ok done => done.state.getReg .x10 == 42 && done.steps == 3 | _ => false)
  check "should reject a program when fuel is insufficient"
    (match runUntil arithmetic 0 2 initial with | .error .fuelExhausted => true | _ => false)
  check "should reject a misaligned instruction address"
    (match step arithmetic { initial with pc := 0x10002 } with
      | .error .instructionMisaligned => true | _ => false)

private def testMemory : IO Unit := do
  check "should load little-endian bytes from an aligned region"
    (match memory.load 8 0x20000 with
      | .ok value => value == 0x0807060504030201 | _ => false)
  check "should reject an access crossing the region end"
    (match memory.load 8 0x20008 with | .error .memoryBounds => true | _ => false)
  check "should reject a misaligned doubleword access"
    (match memory.load 8 0x20001 with | .error .memoryMisaligned => true | _ => false)
  let readOnly : Memory :=
    { regions := #[{ base := 0x20000, bytes := #[1, 2], writable := false }] }
  check "should reject a store into a read-only region"
    (match readOnly.store 1 0x20000 9 with | .error .readOnlyMemory => true | _ => false)

private def testEncoding : IO Unit := do
  check "should encode addi a0 zero 42 as the standard RV64 instruction"
    (match encode (.ADDI .x10 .x0 42) with | .ok word => word == 0x02a00513 | _ => false)
  check "should encode ret as jalr zero ra zero"
    (match encode (.JALR .x0 .x1 0) with | .ok word => word == 0x00008067 | _ => false)
  check "should reject an odd branch displacement"
    (match encode (.BEQ .x0 .x0 3) with | .error .oddDisplacement => true | _ => false)

def main : IO Unit := do
  testRegisters
  testExecution
  testMemory
  testEncoding
  Libp2pAsm.Tests.Machine.run
  Libp2pAsm.Tests.Limits.run
  Libp2pAsm.Tests.Clock.run
  Libp2pAsm.Tests.ClockAsm.run
  Libp2pAsm.Tests.Codec.run
  Libp2pAsm.Tests.Der.run
  Libp2pAsm.Tests.Identity.run
  Libp2pAsm.Tests.CertificateTime.run
  Libp2pAsm.Tests.CertificateAlgorithms.run
  Libp2pAsm.Tests.CertificateUnit.run
  Libp2pAsm.Tests.AsmCodec.run
  Libp2pAsm.Tests.Buffer.run
  Libp2pAsm.Tests.Crypto.run
