import Libp2pAsm.Asm.Quic.Wire.Common

namespace Libp2pAsm.Asm.Quic.Wire
open Rv64 Crypto.Util

private def cid (word : Nat) : P := seq [readByte, li .x7 20,
  reject (.ltu .x7 .x10), storeView word]

private def shortPacket : P := seq [li .x7 20, reject (.ltu .x7 .x26) 10,
  getWord .x5 2, ins [.ANDI .x5 .x5 64], reject (.eq .x5 .x0) 2,
  mov .x10 .x26, storeView 4, put 10 .x22, rest,
  reject (.eq .x10 .x0) 1, put 11 .x10, mov .x22 .x9, publish]

private def retryPacket : P := seq [rest, li .x7 17, reject (.ltu .x10 .x7) 1,
  ins [.ADDI .x10 .x10 (-16)], storeView 8, li .x10 16, storeView 12, publish]

private def vnPacket : P := seq [putN 1 5, rest, reject (.eq .x10 .x0) 2,
  ins [.ANDI .x5 .x10 3], reject (.ne .x5 .x0) 2, storeView 12, publish]

private def v1Packet : P := seq [getWord .x5 2, ins [.ANDI .x7 .x5 64],
  reject (.eq .x7 .x0) 2,
  ins [.SRLI .x24 .x5 4, .ANDI .x24 .x24 3, .ADDI .x5 .x24 1], put 1 .x5,
  li .x7 3, .ite (.eq .x24 .x7) retryPacket emptyP,
  .ite (.eq .x24 .x0) (seq [readInt, storeView 8]) emptyP,
  readInt, reject (.eq .x10 .x0) 2, storeView 10, publish]

private def longPacket : P := seq [readBE 4, put 3 .x10, cid 4, cid 6,
  getWord .x24 3,
  .ite (.eq .x24 .x0) vnPacket emptyP,
  li .x7 1, .ite (.ne .x24 .x7)
    (seq [putN 1 6, rest, storeView 12, publish]) emptyP,
  v1Packet]

/-- One unauthenticated envelope. a6 is negotiated short-header destination CID length. -/
def packetParse : Except String SAsm.Stmt := link (seq [enter 128,
  readByte, put 2 .x10, ins [.ANDI .x5 .x10 128],
  .ite (.eq .x5 .x0) shortPacket emptyP, longPacket])

end Libp2pAsm.Asm.Quic.Wire
