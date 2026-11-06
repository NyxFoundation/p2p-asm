import Libp2pAsm.Asm.Quic.Wire.Common

namespace Libp2pAsm.Asm.Quic.Wire
open Rv64 Crypto.Util

private def scalars (n : Nat) : P := seq <|
  ((List.range n).map fun i => readStore (i+2)) ++ [publish]

private def streamCount : P := seq [readStore 2, li .x7 (2^60),
  reject (.ltu .x7 .x10), publish]

def offsetBound (word : Nat) : P := seq [getWord .x5 word, li .x7 (2^62-1),
  ins [.SUB .x7 .x7 .x5], reject (.ltu .x7 .x10)]

private def stream : P := seq [readStore 2,
  ins [.ANDI .x5 .x24 4], .ite (.ne .x5 .x0) (readStore 3) emptyP,
  ins [.ANDI .x5 .x24 2], .ite (.ne .x5 .x0) readInt rest,
  offsetBound 3, storeView 4, publish]

private def crypto : P := seq [readStore 2, readInt, offsetBound 2, storeView 3, publish]
private def token : P := seq [readInt, reject (.eq .x10 .x0), storeView 2, publish]

private def newCid : P := seq [readStore 2, readStore 3,
  getWord .x5 2, reject (.ltu .x5 .x10), readByte,
  reject (.eq .x10 .x0), li .x7 20, reject (.ltu .x7 .x10),
  storeView 4, li .x10 16, storeView 6, publish]

private def close : P := seq [readStore 2, li .x7 28,
  .ite (.eq .x24 .x7) (readStore 3) emptyP,
  readInt, storeView 4, publish]

/-- Extend staging only after count <= remaining/2 and representable workspace size. -/
private def ackSpace : P := seq [getWord .x25 4,
  rest, ins [.SRLI .x10 .x10 1], reject (.ltu .x10 .x25) 1,
  reject (.geu .x25 .x27) 5,
  li .x7 ((2^64-145)/16), reject (.ltu .x7 .x25) 5,
  ins [.SLLI .x7 .x25 4, .ADDI .x7 .x7 144],
  reject (.ltu .x19 .x7) 5, reject (.ltu .x21 .x7) 5,
  mov .x23 .x7,
  ins [.ADDI .x10 .x20 128, .ADDI .x11 .x23 (-128)], .asm (wipe .x10 .x11)]

private def ackPair : P := seq [readInt, ins [.SD .x2 .x10 120], readInt,
  ins [.LD .x5 .x2 120, .LD .x6 .x2 128, .ADDI .x5 .x5 2],
  reject (.ltu .x6 .x5), ins [.SUB .x6 .x6 .x5], reject (.ltu .x6 .x10),
  ins [.SUB .x5 .x6 .x10, .SD .x2 .x5 128, .LD .x7 .x2 136,
    .SD .x7 .x5 0, .SD .x7 .x6 8, .ADDI .x7 .x7 16, .SD .x2 .x7 136,
    .ADDI .x25 .x25 (-1)]]

private def ack : P := seq [readStore 2, readStore 3, readStore 4, readStore 5,
  getWord .x5 2, reject (.ltu .x5 .x10), ackSpace,
  getWord .x5 2, getWord .x6 5,
  ins [.SUB .x6 .x5 .x6, .SD .x20 .x6 128, .SD .x20 .x5 136,
    .SD .x2 .x6 128, .ADDI .x7 .x20 144, .SD .x2 .x7 136],
  put 9 .x22,
  .loop (.ne .x25 .x0) ackPair,
  getWord .x5 9, ins [.SUB .x5 .x22 .x5], put 10 .x5,
  li .x7 3, .ite (.eq .x24 .x7) (seq [readStore 6,readStore 7,readStore 8]) emptyP,
  publish]

private def dispatch : P := seq [
  li .x7 8, .ite (.geu .x24 .x7) (seq [li .x7 16,
    .ite (.ltu .x24 .x7) (.call 1) emptyP]) emptyP,
  seq (([0,1,30].map fun n => seq [li .x7 n, .ite (.eq .x24 .x7) publish emptyP])),
  seq (([2,3].map fun n => seq [li .x7 n, .ite (.eq .x24 .x7) (.call 2) emptyP])),
  seq (([(4,3),(5,2),(16,1),(17,2),(20,1),(21,2),(25,1)].map fun (n,k) =>
    seq [li .x7 n, .ite (.eq .x24 .x7) (scalars k) emptyP])),
  seq (([18,19,22,23].map fun n => seq [li .x7 n,
    .ite (.eq .x24 .x7) streamCount emptyP])),
  li .x7 6, .ite (.eq .x24 .x7) crypto emptyP,
  li .x7 7, .ite (.eq .x24 .x7) token emptyP,
  li .x7 24, .ite (.eq .x24 .x7) newCid emptyP,
  seq (([26,27].map fun n => seq [li .x7 n,
    .ite (.eq .x24 .x7) (seq [li .x10 8,storeView 2,publish]) emptyP])),
  seq (([28,29].map fun n => seq [li .x7 n, .ite (.eq .x24 .x7) close emptyP])),
  fail 7]

def frameParse : Except String SAsm.Stmt := link
  (seq [enter 128, readInt, put 1 .x10, mov .x24 .x10, dispatch]) [stream,ack]

end Libp2pAsm.Asm.Quic.Wire
