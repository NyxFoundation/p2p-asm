import Libp2pAsm.Rv64.Encoding

namespace Libp2pAsm.Codegen

open Rv64

def assembly (code : Array Instr) : String :=
  ".option norvc\n.option norelax\n.section .text.protocol, \"ax\", @progbits\n" ++
  ".balign 4\n.global protocol_entry\n.type protocol_entry, @function\nprotocol_entry:\n" ++
  String.join (code.toList.map (fun i => s!"  {LeanAsm.Rv64.emitInstr i}\n")) ++
  ".size protocol_entry, . - protocol_entry\n"

def byteHex (b : UInt8) : String :=
  let digits := "0123456789abcdef".toList.toArray
  String.ofList [digits[b.toNat / 16]!, digits[b.toNat % 16]!]

def hexBytes (bytes : ByteArray) : String :=
  String.join (bytes.data.toList.map byteHex)

end Libp2pAsm.Codegen
