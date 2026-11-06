import Libp2pAsm.Asm.Quic.Wire.Writer

namespace Libp2pAsm.Asm.Quic.Wire
open Rv64 Crypto.Util
namespace TransportEncoder
open Writer

private def intBounds (id : Nat) : P := seq [
  li .x7 (2^62-1), reject (.ltu .x7 .x10),
  if id == 3 then seq [li .x7 1200,reject (.ltu .x10 .x7)] else emptyP,
  if id == 8 then seq [li .x7 (2^60),reject (.ltu .x7 .x10)] else emptyP,
  if id == 10 then seq [li .x7 20,reject (.ltu .x7 .x10)] else emptyP,
  if id == 11 then seq [li .x7 (2^14),reject (.geu .x10 .x7)] else emptyP,
  if id == 14 then seq [li .x7 2,reject (.ltu .x10 .x7)] else emptyP]

private def width : P := seq [ins [.LD .x10 .x2 112, .SRLI .x5 .x10 6],
  .ite (.eq .x5 .x0) (li .x10 1) (seq [ins [.SRLI .x5 .x10 14],
    .ite (.eq .x5 .x0) (li .x10 2) (seq [ins [.SRLI .x5 .x10 30],
      .ite (.eq .x5 .x0) (li .x10 4) (li .x10 8)])])]

private def parameter (id : Nat) : P := seq [field (4+2*id),intBounds id,
  ins [.SD .x2 .x10 112],byteN id,width,byte,ins [.LD .x10 .x2 112],integer]

private def bytesParameter (id : Nat) : P := seq [field (5+2*id),li .x7 (if id == 2 then 16 else 20),
  if id == 2 then reject (.ne .x10 .x7) else reject (.ltu .x7 .x10),
  byteN id,integerField (5+2*id),viewField (4+2*id)]

private def optional (id : Nat) : P := seq [field 2,li .x7 (2^id),
  ins [.AND .x5 .x10 .x7], .ite (.ne .x5 .x0) (seq [
    reject (.eq .x26 .x0) 9,bytesParameter id]) emptyP]

def root : P := seq [Writer.enter 512,li .x7 2,reject (.geu .x26 .x7) 10,
  field 2,li .x7 (2^17),reject (.geu .x10 .x7) 10,
  li .x7 (2^13),ins [.AND .x5 .x10 .x7],reject (.ne .x5 .x0) 10,
  seq ([1,3,4,5,6].map parameter),
  byteN 7,byteN 1,byteN 0,parameter 8,byteN 9,byteN 1,byteN 0,
  seq ([10,11,14].map parameter),byteN 12,byteN 0,bytesParameter 15,
  optional 0,optional 16,optional 2,finish]

end TransportEncoder

def transportEncode : Except String SAsm.Stmt := Writer.link TransportEncoder.root
end Libp2pAsm.Asm.Quic.Wire
