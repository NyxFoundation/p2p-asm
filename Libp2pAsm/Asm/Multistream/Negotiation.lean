import Libp2pAsm.Asm.Multistream.Framing

namespace Libp2pAsm.Asm.Multistream
open Rv64 Crypto.Util Libp2pAsm.Asm.Stream

private def prepare : SAsm.Stmt := seq [preflight 120, sourceView,
  b [.LD .x5 .x8 112], guard (.geu .x16 .x5) 10,
  b [.ADDI .x13 .x15 0, .ADDI .x14 .x0 0,
    .LD .x9 .x8 0, .LD .x18 .x8 8, .LD .x19 .x8 16,
    .LD .x20 .x8 24, .LD .x21 .x8 32, .LD .x22 .x8 40,
    .LD .x23 .x8 48, .LD .x24 .x8 56, .LD .x25 .x8 64,
    .LD .x16 .x8 72, .LD .x26 .x8 80, .LD .x27 .x8 88,
    .LD .x17 .x8 96, .LD .x11 .x8 104,
    .ADDI .x5 .x0 (-1), .SRLI .x5 .x5 1],
  guard (.eq .x9 .x0), guard (.ltu .x5 .x9), guard (.eq .x18 .x0),
  guard (.ltu .x18 .x19), b [.ADDI .x5 .x0 1],
  guard (.ltu .x5 .x20), guard (.ltu .x5 .x11),
  b [.ADDI .x5 .x0 3], guard (.ltu .x5 .x21),
  guard (.ltu .x5 .x26), guard (.ltu .x9 .x24), guard (.ltu .x9 .x25),
  b [.ADDI .x5 .x0 56], guard (.ltu .x5 .x23),
  b [.ADDI .x5 .x0 7, .REMU .x5 .x23 .x5], guard (.ne .x5 .x0),
  b [.ADDI .x10 .x0 0]]

/-- Commit staged scalar parsing state only after the entire accepted fragment.
Output a1=consumed bytes, a2=response kind, a3=selected Ping. -/
private def commit : SAsm.Stmt := seq [b [
  .SD .x8 .x19 16, .SD .x8 .x21 32, .SD .x8 .x22 40,
  .SD .x8 .x23 48, .SD .x8 .x24 56, .SD .x8 .x25 64,
  .SD .x8 .x16 72, .SD .x8 .x26 80, .SD .x8 .x27 88,
  .SD .x8 .x17 96, .SD .x8 .x11 104,
  .ADDI .x12 .x10 0, .ADDI .x11 .x14 0, .ADDI .x10 .x0 0,
  .ADDI .x13 .x0 0, .ADDI .x14 .x0 0, .ADDI .x5 .x0 2],
  .ite (.eq .x21 .x5) (b [.ADDI .x13 .x0 1]) nil, exit true]

private def resetFrame : SAsm.Stmt := b [
  .ADDI .x22 .x0 0, .ADDI .x23 .x0 0, .ADDI .x24 .x0 0,
  .ADDI .x25 .x0 0, .ADDI .x16 .x0 0, .ADDI .x26 .x0 0,
  .ADDI .x27 .x0 128, .ADDI .x17 .x0 191, .ADDI .x11 .x0 0]

private def completeFrame : SAsm.Stmt := seq [
  b [.ADDI .x5 .x0 10], guard (.ne .x15 .x5) 13, guard (.ne .x26 .x0) 13,
  .ite (.eq .x21 .x0) (seq [b [.ANDI .x5 .x16 1], guard (.eq .x5 .x0) 13,
    b [.ADDI .x21 .x0 1]])
    (.ite (.eq .x20 .x0) (seq [b [.ANDI .x5 .x16 2],
      .ite (.eq .x5 .x0) (seq [b [.ANDI .x5 .x16 4],
        .ite (.ne .x5 .x0) (fail 9) (fail 13)]) nil, b [.ADDI .x21 .x0 2]])
      (seq [guard (.geu .x19 .x18) 14, b [.ADDI .x19 .x19 1, .ANDI .x5 .x16 2],
        .ite (.ne .x5 .x0) (b [.ADDI .x21 .x0 2, .ADDI .x10 .x0 2])
          (b [.ADDI .x10 .x0 3])])), resetFrame, commit]

private def payloadByte : SAsm.Stmt := seq [
  utf8, matchText header 1, matchText ping 2, matchText na 4,
  b [.ADDI .x24 .x24 (-1), .ADDI .x25 .x25 1],
  .ite (.eq .x24 .x0) completeFrame nil,
  b [.ADDI .x5 .x0 10], guard (.eq .x15 .x5) 13]

private def prefixByte : SAsm.Stmt := seq [
  b [.ANDI .x5 .x15 127, .SLL .x6 .x5 .x23, .OR .x22 .x22 .x6,
    .ADDI .x6 .x0 128],
  .ite (.ltu .x15 .x6) (seq [
    .ite (.ne .x23 .x0) (guard (.eq .x5 .x0) 13) nil,
    guard (.eq .x22 .x0) 13, guard (.ltu .x9 .x22) 13,
    b [.ADDI .x11 .x0 1, .ADDI .x24 .x22 0, .ADDI .x23 .x0 0,
      .ADDI .x16 .x0 0, .ADDI .x5 .x0 (imm header.length)],
    .ite (.eq .x22 .x5) (b [.ORI .x16 .x16 1]) nil,
    b [.ADDI .x5 .x0 (imm ping.length)],
    .ite (.eq .x22 .x5) (b [.ORI .x16 .x16 2]) nil,
    b [.ADDI .x5 .x0 3], .ite (.eq .x22 .x5) (b [.ORI .x16 .x16 4]) nil])
    (seq [b [.ADDI .x5 .x0 56], guard (.eq .x23 .x5) 13,
      b [.ADDI .x23 .x23 7]])]

/-- Processes at most one frame; caller dispatches returned leftover immediately.
No negotiation payload buffer: only bounded framing/UTF8/matching scalar state. -/
def feed : Except String SAsm.Stmt := Crypto.Link.program
  (.seq [.asm (seq [prepare,
    b [.ADDI .x5 .x0 3], guard (.eq .x21 .x5) 9,
    b [.ADDI .x5 .x0 2], .ite (.eq .x21 .x5) commit nil]),
    .loop (.ltu .x14 .x13) (.seq [
      .asm (b [.LBU .x15 .x12 0, .ADDI .x12 .x12 1, .ADDI .x14 .x14 1]),
      .ite (.eq .x11 .x0) (.call 0) (.call 1)]), .asm commit])
  [.asm (seq [prefixByte, .ret]), .asm (seq [payloadByte, .ret])]

/-- Deadline dispatched by caller monotonic clock, never inferred from packets.
Returns a4=1 when newly expired, with terminal state and cleared parser scalars. -/
def timer : SAsm.Stmt := seq [preflight 120,
  b [.LD .x5 .x8 112, .LD .x6 .x8 32, .ADDI .x7 .x0 2],
  .ite (.geu .x6 .x7) (seq [zeroOutputs, exit true]) nil,
  .ite (.ltu .x12 .x5) (seq [zeroOutputs, exit true]) nil,
  b [.ADDI .x5 .x0 3, .SD .x8 .x5 32] ,
  b ((List.range 9).map fun i => .SD .x8 .x0 (imm (40+8*i))),
  b [.ADDI .x5 .x0 128, .SD .x8 .x5 88, .ADDI .x5 .x0 191, .SD .x8 .x5 96],
  zeroOutputs, b [.ADDI .x14 .x0 1], exit true]

end Libp2pAsm.Asm.Multistream
