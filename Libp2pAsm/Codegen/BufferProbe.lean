import Libp2pAsm.Asm.Buffer
import Libp2pAsm.Codegen.Input
import Libp2pAsm.Rv64.Execution

namespace Libp2pAsm.Codegen

/-- Test-only image contains the table and reference. Resolved payloads are not dereferenced. -/
def evalBuffer (hex offset count write : String) : Option ByteArray := do
  let bytes ← parseHex hex
  let refOffset ← parseWord offset
  let slots ← parseWord count
  let access ← parseWord write
  if refOffset.toNat % 8 != 0 || refOffset.toNat + 32 > bytes.length then none else do
    let memory : Rv64.Memory :=
      { regions := #[{ base := 0x20000, bytes := bytes.toArray, writable := false }] }
    let s : Rv64.State := { pc := 0x10000, memory := memory }
    let input := (((s.setReg .x10 0x20000).setReg .x11 (0x20000 + refOffset)).setReg .x12 slots)
      |>.setReg .x13 access
    let code ← Asm.resolveBuffer.lower.toOption
    let done ← (Rv64.runUntil { base := 0x10000, code := code } 0 128 input).toOption
    let registers := [.x10, .x11, .x12].map done.state.getReg
    return wordBytes registers ++ ⟨bytes.toArray⟩

end Libp2pAsm.Codegen
