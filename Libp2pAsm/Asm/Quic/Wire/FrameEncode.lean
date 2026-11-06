import Libp2pAsm.Asm.Quic.Wire.Writer

namespace Libp2pAsm.Asm.Quic.Wire
open Rv64 Crypto.Util
namespace FrameEncoder
open Writer

private def scalars (n : Nat) : P := seq <|
  (List.range n).map (fun i => integerField (i+2)) ++ [Writer.finish]

private def count : P := seq [field 2, li .x7 (2^60), reject (.ltu .x7 .x10),
  integer, finish]

private def offsetLength (offset length : Nat) : P := seq [saveField offset 112,
  field length, ins [.LD .x5 .x2 112], li .x7 (2^62-1), reject (.ltu .x7 .x5),
  ins [.SUB .x7 .x7 .x5], reject (.ltu .x7 .x10)]

private def stream : P := seq [integerField 2, offsetLength 3 5,
  ins [.ANDI .x5 .x24 4],
  .ite (.ne .x5 .x0) (integerField 3) (seq [field 3, reject (.ne .x10 .x0)]),
  ins [.ANDI .x5 .x24 2], .ite (.ne .x5 .x0) (integerField 5) emptyP,
  viewField 4, finish]

private def crypto : P := seq [offsetLength 2 4, integerField 2, integerField 4,
  viewField 3, finish]
private def token : P := seq [field 3, reject (.eq .x10 .x0), integer,
  viewField 2, finish]

private def newCid : P := seq [saveField 2 112, field 3,
  ins [.LD .x5 .x2 112], reject (.ltu .x5 .x10), integerField 2, integerField 3,
  field 5, reject (.eq .x10 .x0), li .x7 20, reject (.ltu .x7 .x10), byte,
  viewField 4, field 7, li .x7 16, reject (.ne .x10 .x7), viewField 6, finish]

private def path : P := seq [field 3, li .x7 8, reject (.ne .x10 .x7),
  viewField 2,finish]
private def close : P := seq [integerField 2, li .x7 28,
  .ite (.eq .x24 .x7) (integerField 3) emptyP, integerField 5, viewField 4,finish]

private def ackSetup : P := seq [saveField 2 112, saveField 5 120,
  ins [.LD .x5 .x2 112], reject (.ltu .x5 .x10), saveField 4 128,
  reject (.geu .x10 .x27) 5,
  li .x7 144, reject (.ltu .x9 .x7) 1,
  ins [.ADDI .x5 .x9 (-144), .SRLI .x5 .x5 4], reject (.ltu .x5 .x10) 1,
  mov .x25 .x10,
  field 16, ins [.LD .x5 .x2 112, .LD .x6 .x2 120, .SUB .x5 .x5 .x6],
  reject (.ne .x5 .x10), ins [.SD .x2 .x10 136],
  field 17, ins [.LD .x5 .x2 112], reject (.ne .x5 .x10),
  integerField 2, integerField 3, integerField 4, integerField 5, li .x26 144]

private def ackPair : P := seq [ins [.SD .x2 .x1 192],mov .x10 .x26, fieldAt, ins [.SD .x2 .x10 144],
  ins [.ADDI .x10 .x26 8], fieldAt, ins [.SD .x2 .x10 152, .LD .x5 .x2 144],
  reject (.ltu .x10 .x5), li .x7 (2^62-1), reject (.ltu .x7 .x10),
  ins [.LD .x6 .x2 136], li .x7 2, reject (.ltu .x6 .x7),
  ins [.ADDI .x6 .x6 (-2)], reject (.ltu .x6 .x10),
  ins [.SUB .x10 .x6 .x10], integer,
  ins [.LD .x10 .x2 152, .LD .x5 .x2 144, .SUB .x10 .x10 .x5], integer,
  ins [.LD .x5 .x2 144, .SD .x2 .x5 136, .ADDI .x26 .x26 16, .ADDI .x25 .x25 (-1),
    .LD .x1 .x2 192],.asm .ret]

private def ack : P := seq [ackSetup, .loop (.ne .x25 .x0) (.call 5),
  li .x7 3, .ite (.eq .x24 .x7) (seq [integerField 6,integerField 7,integerField 8]) emptyP,
  finish]

private def dispatch : P := seq [
  li .x7 8, .ite (.geu .x24 .x7) (seq [li .x7 16,
    .ite (.ltu .x24 .x7) (.call 2) emptyP]) emptyP,
  seq ([0,1,30].map fun n => seq [li .x7 n, .ite (.eq .x24 .x7) finish emptyP]),
  seq ([2,3].map fun n => seq [li .x7 n, .ite (.eq .x24 .x7) (.call 3) emptyP]),
  seq ([(4,3),(5,2),(16,1),(17,2),(20,1),(21,2),(25,1)].map fun (n,k) =>
    seq [li .x7 n, .ite (.eq .x24 .x7) (scalars k) emptyP]),
  seq ([18,19,22,23].map fun n => seq [li .x7 n, .ite (.eq .x24 .x7) count emptyP]),
  li .x7 6, .ite (.eq .x24 .x7) crypto emptyP,
  li .x7 7, .ite (.eq .x24 .x7) token emptyP,
  li .x7 24, .ite (.eq .x24 .x7) (.call 4) emptyP,
  seq ([26,27].map fun n => seq [li .x7 n, .ite (.eq .x24 .x7) path emptyP]),
  seq ([28,29].map fun n => seq [li .x7 n, .ite (.eq .x24 .x7) close emptyP]),
  fail 7]

def root : P := seq [Writer.enter 128, field 1, mov .x24 .x10,
  li .x7 30, reject (.ltu .x7 .x24) 7, integer, dispatch]

def build : Except String SAsm.Stmt := Writer.link root [stream,ack,newCid,ackPair]
end FrameEncoder

def frameEncode : Except String SAsm.Stmt := FrameEncoder.build
end Libp2pAsm.Asm.Quic.Wire
