import Libp2pAsm.Asm.Crypto.Curve25519.Common
import Libp2pAsm.Spec.Crypto.Curve25519.Field
import Tests.AsmCrypto.Support
import Tests.AsmCrypto.Trace

namespace Libp2pAsm.Tests.Curve25519
open Rv64 Asm.Crypto.Curve25519 Asm.Crypto.Util Asm.Crypto.Link
open AsmCrypto (check snapshot)

private def wrapper (op : Nat) : Except String SAsm.Stmt := program (.seq [
  .asm enter, .asm (block [.ADDI .x8 .x10 0, .ADDI .x9 .x11 0,
    .ADDI .x18 .x12 0, .ADDI .x19 .x13 0]),
  .asm (block [.ADDI .x10 .x19 0, .ADDI .x11 .x8 0]), .call 3,
  .asm (block [.ADDI .x10 .x19 40, .ADDI .x11 .x9 0]), .call 3,
  fieldCall op .x19 80 0 40,
  .asm (block [.ADDI .x10 .x18 0, .ADDI .x11 .x19 80]), .call 4,
  .asm (block [.ADDI .x11 .x0 120]), .asm (wipe .x19 .x11),
  .asm (block [.ADDI .x10 .x0 0]), .asm leave]) fieldCallees

private def runOne (p : Program) (op a b : Nat) : IO Unit := do
  let bytes := fun n => (Spec.Crypto.Curve25519.encodeLE n 32).toArray
  let memory : Memory := { regions := #[
    ⟨0x20000, AsmCrypto.guarded (bytes a), false⟩,
    ⟨0x30000, AsmCrypto.guarded (bytes b), false⟩,
    ⟨0x40000, AsmCrypto.guarded (Array.replicate 32 0xcc), true⟩,
    ⟨0x50000, AsmCrypto.guarded (Array.replicate 120 0xcc), true⟩,
    ⟨0x60000, Array.replicate 176 0x69, true⟩] }
  let s : State := { pc := 0x10000, memory := memory, regs := Vector.ofFn (AsmCrypto.seedReg 0)}
  let s := (s.setReg .x1 0x18000).setReg .x2 0x600a0
  let s := (s.setReg .x10 0x20008).setReg .x11 0x30008
  let s := (s.setReg .x12 0x40008).setReg .x13 0x50008
  let .ok done := runUntil p 0x18000 20000 s | throw (IO.userError "field execution")
  let f := match op with
    | 0 => Spec.Crypto.Curve25519.add | 1 => Spec.Crypto.Curve25519.sub
    | _ => Spec.Crypto.Curve25519.mul
  let expected := bytes (f (a%2^255%Spec.Crypto.Curve25519.prime)
    (b%2^255%Spec.Crypto.Curve25519.prime))
  let result := ((done.state.memory.regions[2]?).getD (⟨0,#[],false⟩ : Region)).bytes.extract 8 40
  check s!"field operation {op} {a} {b}" (result == expected)

end Libp2pAsm.Tests.Curve25519

open Libp2pAsm in
def main : IO Unit := do
  for op in [0,1,2] do
    let .ok stmt := Tests.Curve25519.wrapper op | throw (IO.userError "link")
    let .ok code := stmt.lower | throw (IO.userError "lower")
    for a in [0,1,18,19,2^51-1,2^255-20,2^255-19,2^255-1,2^256-1] do
      for b in [0,1,2^51-1,2^255-20,2^255-1] do
        Tests.Curve25519.runOne ⟨0x10000,code⟩ op a b
  IO.println "PASS: field boundary products/additions/subtractions"
