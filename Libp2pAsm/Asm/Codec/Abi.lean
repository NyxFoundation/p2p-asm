import Libp2pAsm.Asm.Basic

namespace Libp2pAsm.Asm.Codec

open Rv64

/-- Decoder scratch ABI: x28 contains the value and x6 the consumed width. -/
def decodeSuccess : SAsm.Stmt :=
  .seq (.block [.ADDI .x11 .x28 0, .ADDI .x12 .x6 0, .ADDI .x10 .x0 0]) .ret

/-- Encoder scratch ABI: x31 contains the written byte count. -/
def encodeSuccess : SAsm.Stmt :=
  .seq (.block [.ADDI .x11 .x31 0, .ADDI .x12 .x0 0, .ADDI .x10 .x0 0]) .ret

end Libp2pAsm.Asm.Codec
