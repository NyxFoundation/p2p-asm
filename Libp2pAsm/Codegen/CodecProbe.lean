import Libp2pAsm.Asm.Codec.QuicVarint
import Libp2pAsm.Asm.Codec.UnsignedVarint
import Libp2pAsm.Codegen.Input
import Libp2pAsm.Rv64.Execution

namespace Libp2pAsm.Codegen

def codecRoutine (name : String) : Option Rv64.SAsm.Stmt :=
  match name with
  | "quic-encode" => some Asm.Codec.QuicVarint.encode
  | "quic-decode" => some Asm.Codec.QuicVarint.decode
  | "uvarint-encode" => some Asm.Codec.UnsignedVarint.encode
  | "uvarint-decode" => some Asm.Codec.UnsignedVarint.decode
  | _ => none

private def initial (name argument limit : String) : Option Rv64.State := do
  let bound ← parseWord limit
  if bound.toNat > 1024 then none else do
    let encoding := name == "quic-encode" || name == "uvarint-encode"
    let value ← if encoding then parseWord argument else some 0
    let bytes ← if encoding then some (List.replicate (bound.toNat + 2) 0xaa)
      else parseHex argument
    if !encoding && bound.toNat > bytes.length then none else do
      let memory : Rv64.Memory := if bytes.isEmpty then {} else
        { regions := #[{ base := 0x20000, bytes := bytes.toArray, writable := encoding }] }
      let s : Rv64.State := { pc := 0x10000, memory := memory }
      let a0 := if encoding then value else 0x20000
      let a1 := if encoding then 0x20001 else bound
      return ((s.setReg .x10 a0).setReg .x11 a1).setReg .x12 (if encoding then bound else 0)

/-- Test-facing interpreter output: a0/a1/a2 in LE64 followed by all buffer bytes. -/
def evalCodec (name argument limit : String) : Option ByteArray := do
  let body ← codecRoutine name
  let s ← initial name argument limit
  let code ← body.lower.toOption
  let done ← (Rv64.runUntil { base := 0x10000, code := code } 0 512 s).toOption
  let registers := [.x10, .x11, .x12].map done.state.getReg
  return done.state.memory.regions.foldl
    (fun out region => out ++ ⟨region.bytes⟩) (wordBytes registers)

end Libp2pAsm.Codegen
