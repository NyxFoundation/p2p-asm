import Libp2pAsm.Asm.Quic.Wire.Packet
import Libp2pAsm.Asm.Quic.Wire.Frame

namespace Libp2pAsm.Asm.Quic.Wire
open Rv64 Crypto.Util

private def stackPreflight : P := seq [li .x7 512,earlyReject (.ltu .x2 .x7) 4,
  ins [.ADDI .x28 .x2 (-512)],disjoint .x28 .x7 .x10 .x11,
  disjoint .x28 .x7 .x12 .x13,disjoint .x28 .x7 .x14 .x15]

private def allocate (packets : Bool) : P := seq [
  if packets then li .x10 144 else seq [li .x7 ((2^64-145)/16),
    reject (.ltu .x7 .x26) 5,ins [.SLLI .x10 .x26 4,.ADDI .x10 .x10 144]],
  ins [.SD .x2 .x10 112,.ADDI .x5 .x10 (-16),.SD .x2 .x5 120,
    .MULHU .x7 .x27 .x10],reject (.ne .x7 .x0) 5,
  ins [.MUL .x10 .x27 .x10],li .x7 (2^64-17),reject (.ltu .x7 .x10) 5,
  ins [.ADDI .x10 .x10 16],reject (.ltu .x19 .x10) 5,
  reject (.ltu .x21 .x10) 5,ins [.SUB .x7 .x21 .x10,.LD .x5 .x2 120],
  reject (.ltu .x7 .x5) 5,mov .x23 .x10,
  ins [.ADD .x10 .x10 .x5],.asm (wipe .x20 .x10),li .x24 0]

private def childError : P := seq [ins [.SD .x2 .x10 128,.ADD .x22 .x22 .x11],
  .asm (wipe .x20 .x23),ins [.LD .x10 .x2 128],mov .x11 .x22,li .x12 0,leave]

private def one (packets : Bool) : P := seq [reject (.geu .x24 .x27) 5,
  ins [.LD .x5 .x2 112,.MUL .x5 .x24 .x5,.ADD .x12 .x20 .x5,
    .SD .x12 .x22 16,.ADDI .x12 .x12 24,
    .ADD .x10 .x8 .x22,.SUB .x11 .x9 .x22,
    .LD .x13 .x2 120,.ADD .x14 .x20 .x23,.ADDI .x15 .x13 0],
  if packets then seq [mov .x16 .x26,li .x17 0]
    else seq [li .x16 0,mov .x17 .x26],
  .call 0,.ite (.ne .x10 .x0) childError emptyP,
  ins [.ADD .x22 .x22 .x12,.ADDI .x24 .x24 1]]

/-- a6=short CID length (packet batch), or ACK range capacity (frame batch).
a7=batch capacity. Stack mapping must include 512 bytes. Publication is atomic
across the batch; each leaf retains its one-packet/frame truncation semantics. -/
def batchParse (packets : Bool) : Except String SAsm.Stmt := do
  let child ← if packets then packetParse else frameParse
  Crypto.Link.program (seq [stackPreflight,enter 16,allocate packets,
    .loop (.ltu .x22 .x9) (one packets),put 1 .x24,publish]) [.asm child]

end Libp2pAsm.Asm.Quic.Wire
