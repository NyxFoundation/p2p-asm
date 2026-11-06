import Libp2pAsm.Asm.Quic.Wire.Writer

namespace Libp2pAsm.Asm.Quic.Wire
open Rv64 Crypto.Util
namespace PacketEncoder
open Writer

private def cid (word : Nat) : P := seq [field (word+1), li .x7 20,
  reject (.ltu .x7 .x10), byte, viewField word]

private def prefixBytes (first version : Nat) : P := seq [byteN first,
  li .x10 version, be 4, cid 4, cid 6]

private def vn : P := seq [field 13, reject (.eq .x10 .x0) 2,
  ins [.ANDI .x5 .x10 3], reject (.ne .x5 .x0) 2,
  prefixBytes 128 0, viewField 12, finish]

private def retry : P := seq [field 9, reject (.eq .x10 .x0),
  field 13, li .x7 16, reject (.ne .x10 .x7),
  prefixBytes 240 1, viewField 8, viewField 12, finish]

private def pn : P := seq [saveField 14 112, li .x7 1, reject (.ltu .x10 .x7),
  li .x7 4, reject (.ltu .x7 .x10), field 15,
  ins [.LD .x5 .x2 112, .SLLI .x5 .x5 3, .SRL .x5 .x10 .x5],
  reject (.ne .x5 .x0), saveField 15 120]

private def emitPn : P := seq [ins [.LD .x25 .x2 112],
  .loop (.ne .x25 .x0) (seq [ins [.ADDI .x25 .x25 (-1), .SLLI .x5 .x25 3,
    .LD .x10 .x2 120, .SRL .x10 .x10 .x5], byte])]

private def short : P := seq [field 2, li .x7 36,
  ins [.AND .x10 .x10 .x7, .ORI .x10 .x10 64, .LD .x5 .x2 112,
    .ADDI .x5 .x5 (-1), .OR .x10 .x10 .x5], byte,
  field 5, li .x7 20, reject (.ltu .x7 .x10), viewField 4,
  emitPn, viewField 12, finish]

private def long : P := seq [
  ins [.ADDI .x10 .x24 (-1), .SLLI .x10 .x10 4, .ORI .x10 .x10 192,
    .LD .x5 .x2 112, .ADDI .x5 .x5 (-1), .OR .x10 .x10 .x5], byte,
  li .x10 1, be 4, cid 4, cid 6,
  li .x7 1, .ite (.eq .x24 .x7) (seq [integerField 9,viewField 8]) emptyP,
  field 13, li .x7 (2^62-1), ins [.LD .x5 .x2 112, .SUB .x7 .x7 .x5],
  reject (.ltu .x7 .x10), ins [.ADD .x10 .x10 .x5], integer,
  emitPn, viewField 12, finish]

def root : P := seq [Writer.enter 128, field 7, li .x7 20, reject (.ltu .x7 .x10),
  field 2,li .x7 36,ins [.OR .x5 .x10 .x7],reject (.ne .x5 .x7),
  field 1, mov .x24 .x10,
  li .x7 5, reject (.ltu .x7 .x24) 10,
  seq ([4,6,8,12].map checkViewField),
  li .x7 5,
  .ite (.eq .x24 .x7) (.call 2) emptyP,
  li .x7 4, .ite (.eq .x24 .x7) (.call 3) emptyP,
  pn, .ite (.eq .x24 .x0) (.call 4) emptyP, long]

def build : Except String SAsm.Stmt := Writer.link root [vn,retry,short]

end PacketEncoder

def packetEncode : Except String SAsm.Stmt := PacketEncoder.build
end Libp2pAsm.Asm.Quic.Wire
