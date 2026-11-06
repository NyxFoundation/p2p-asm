import Libp2pAsm.Asm.Clock
import Libp2pAsm.Codegen.Input
import Libp2pAsm.Rv64.Execution

namespace Libp2pAsm.Codegen

def evalClock (hex drift span : String) : Option ByteArray := do
  let bytes ← parseHex hex
  if bytes.length != 80 then none else do
    let maxDrift ← parseWord drift
    let maxSpan ← parseWord span
    let memory : Rv64.Memory := { regions := #[
      { base := 0x20000, bytes := bytes.toArray.extract 0 40, writable := true },
      { base := 0x20028, bytes := bytes.toArray.extract 40 80, writable := false }] }
    let initial : Rv64.State := { pc := 0x10000, memory }
    let initial := (((initial.setReg .x10 0x20000).setReg .x11 0x20028)
      |>.setReg .x12 maxDrift).setReg .x13 maxSpan
    let code ← Asm.checkClock.lower.toOption
    let result ← (Rv64.runUntil { base := 0x10000, code } 0 256 initial).toOption
    let output := wordBytes ([.x10, .x11, .x12].map result.state.getReg)
    return result.state.memory.regions.foldl (fun acc r => acc ++ ⟨r.bytes⟩) output

end Libp2pAsm.Codegen
