import Libp2pAsm.Asm.Quic.Wire.Common

namespace Libp2pAsm.Asm.Quic.Wire
open Rv64 Crypto.Util

private def returnAt (slot : Nat) : P := seq [ins [.LD .x1 .x2 (imm slot)],.asm .ret]

private def duplicateScan : P := seq [ins [.SD .x2 .x22 144], li .x22 0,
  ins [.LD .x28 .x2 112],
  .loop (.ltu .x22 .x28) (seq [readInt,
    .ite (.eq .x10 .x24) (seq [ins [.LD .x22 .x2 144], fail 8]) emptyP,
    readInt, take, ins [.LD .x28 .x2 112]]),
  ins [.LD .x22 .x2 144]]

private def header : P := seq [ins [.SD .x2 .x1 192, .SD .x2 .x22 112],
  readInt, mov .x24 .x10, readInt, ins [.SD .x2 .x10 128],
  duplicateScan, ins [.LD .x10 .x2 128], take,
  ins [.SD .x2 .x11 120], returnAt 192]

private def outputPair : P := seq [
  ins [.SLLI .x7 .x24 4, .ADD .x7 .x20 .x7,
    .LD .x5 .x2 120, .LD .x6 .x2 128, .SD .x7 .x5 32, .SD .x7 .x6 40],
  returnAt 200]

private def boundedCid : P := seq [ins [.LD .x5 .x2 128],
  li .x7 20, reject (.ltu .x7 .x5), outputPair]

private def resetToken : P := seq [ins [.LD .x5 .x2 128],
  li .x7 16, reject (.ne .x5 .x7), outputPair]

private def disable : P := seq [ins [.LD .x5 .x2 128], reject (.ne .x5 .x0),
  putN 28 1, returnAt 200]

private def preferred : P := seq [ins [.LD .x5 .x2 128], li .x7 41,
  reject (.ltu .x5 .x7), ins [.LD .x6 .x2 120, .ADD .x7 .x8 .x6, .LBU .x10 .x7 24],
  reject (.eq .x10 .x0), li .x28 20, reject (.ltu .x28 .x10),
  ins [.ADDI .x28 .x10 41], reject (.ne .x5 .x28),
  put 40 .x6, putN 41 4,
  ins [.LD .x6 .x2 120, .ADD .x7 .x8 .x6,
    .LBU .x5 .x7 4, .SLLI .x5 .x5 8, .LBU .x28 .x7 5, .OR .x5 .x5 .x28], put 42 .x5,
  ins [.ADDI .x5 .x6 6], put 43 .x5, putN 44 16,
  ins [.ADD .x7 .x8 .x6, .LBU .x5 .x7 22, .SLLI .x5 .x5 8,
    .LBU .x28 .x7 23, .OR .x5 .x5 .x28], put 45 .x5,
  ins [.ADDI .x5 .x6 25], put 46 .x5, put 47 .x10,
  ins [.ADD .x5 .x5 .x10], put 48 .x5, putN 49 16, outputPair]

private def integerBounds : P := seq [
  li .x7 3, .ite (.eq .x24 .x7) (seq [li .x7 1200, reject (.ltu .x11 .x7)]) emptyP,
  seq ([8,9].map fun n => seq [li .x7 n, .ite (.eq .x24 .x7)
    (seq [li .x7 (2^60), reject (.ltu .x7 .x11)]) emptyP]),
  li .x7 10, .ite (.eq .x24 .x7) (seq [li .x7 20, reject (.ltu .x7 .x11)]) emptyP,
  li .x7 11, .ite (.eq .x24 .x7) (seq [li .x7 (2^14), reject (.geu .x11 .x7)]) emptyP,
  li .x7 14, .ite (.eq .x24 .x7) (seq [li .x7 2, reject (.ltu .x11 .x7)]) emptyP]

private def intValue : P := seq [ins [.LD .x10 .x2 120, .ADD .x10 .x8 .x10,
  .LD .x11 .x2 128], .call 0,
  reject (.ne .x10 .x0) 2, ins [.LD .x5 .x2 128], reject (.ne .x5 .x12) 2,
  integerBounds,
  ins [.SLLI .x7 .x24 4, .ADD .x7 .x20 .x7, .SD .x7 .x11 32], returnAt 200]

private def known : P := seq [ins [.SD .x2 .x1 200],
  .ite (.eq .x26 .x0) (seq ([0,2,13,16].map fun n => seq [li .x7 n,
    reject (.eq .x24 .x7) 9])) emptyP,
  getWord .x5 2, li .x6 1, ins [.SLL .x6 .x6 .x24, .OR .x5 .x5 .x6], put 2 .x5,
  seq ([0,15,16].map fun n => seq [li .x7 n,.ite (.eq .x24 .x7) boundedCid emptyP]),
  li .x7 2, .ite (.eq .x24 .x7) resetToken emptyP,
  li .x7 12, .ite (.eq .x24 .x7) disable emptyP,
  li .x7 13, .ite (.eq .x24 .x7) preferred emptyP,
  intValue]

private def transport : P := seq [enter 512, li .x7 2, reject (.geu .x26 .x7) 10,
  putN 10 65527, putN 24 3, putN 26 25, putN 32 2, li .x25 0,
  .loop (.ltu .x22 .x9) (seq [reject (.geu .x25 .x27) 5,
    .call 1, li .x7 17, .ite (.ltu .x24 .x7) (.call 2) emptyP,
    ins [.ADDI .x25 .x25 1]]),
  put 1 .x25, publish]

def transportParse : Except String SAsm.Stmt := link transport [header,known]

end Libp2pAsm.Asm.Quic.Wire
