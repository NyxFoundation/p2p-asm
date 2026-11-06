import Libp2pAsm.Asm.Stream.Common

namespace Libp2pAsm.Asm.Stream
open Rv64 Crypto.Util

/-- 128 bytes, full field table in Tests/Streams/README.md. -/
def sendState : SAsm.Stmt := seq [preflight 128, b [
  .LD .x9 .x8 0, .LD .x18 .x8 8, .LD .x19 .x8 16,
  .LD .x20 .x8 24, .LD .x21 .x8 32, .LD .x22 .x8 40,
  .LD .x23 .x8 48, .LD .x24 .x8 56, .LD .x25 .x8 64,
  .LD .x26 .x8 88, .LD .x27 .x8 120,
  .ADDI .x7 .x0 (-1), .SRLI .x7 .x7 2],
  guard (.eq .x9 .x0), guard (.ltu .x7 .x9),
  guard (.ltu .x22 .x20), guard (.ltu .x21 .x22), guard (.ltu .x7 .x21),
  guard (.ltu .x7 .x23), guard (.ltu .x7 .x24),
  b [.SUB .x5 .x21 .x20], guard (.ltu .x9 .x5),
  b [.ADDI .x5 .x0 1], guard (.ltu .x5 .x26), guard (.ltu .x5 .x27),
  b [.LD .x6 .x8 72], guard (.ltu .x5 .x6),
  b [.LD .x6 .x8 80], guard (.ltu .x5 .x6),
  b [.ADDI .x5 .x0 (-1)],
  .ite (.ne .x25 .x5) (guard (.ne .x25 .x21)) nil,
  span .x18 .x9, span .x19 .x9]

/-- Queue plaintext only. Neither sent credit nor reservation changes here. -/
def append : SAsm.Stmt := seq [sendState, sourceView,
  b [.ADDI .x5 .x0 1], guard (.ltu .x5 .x16), guard (.ne .x26 .x0) 9,
  b [.ADDI .x5 .x0 (-1)], guard (.ne .x25 .x5) 9,
  b [.SRLI .x5 .x5 2, .SUB .x5 .x5 .x21], guard (.ltu .x5 .x15) 2,
  b [.ADD .x27 .x21 .x15, .SUB .x5 .x27 .x20], guard (.ltu .x9 .x5) 6,
  b [.ADDI .x5 .x21 0], .loop (.ltu .x5 .x27) (b [
    .REMU .x6 .x5 .x9, .ADD .x7 .x18 .x6, .LBU .x28 .x12 0,
    .SB .x7 .x28 0, .ADD .x7 .x19 .x6, .SB .x7 .x0 0,
    .ADDI .x12 .x12 1, .ADDI .x5 .x5 1]),
  b [.SD .x8 .x27 32],
  .ite (.ne .x16 .x0) (b [.SD .x8 .x27 64]) nil,
  zeroOutputs, exit true]

private def rangeEnd : SAsm.Stmt := seq [
  b [.ADDI .x5 .x0 (-1), .SRLI .x5 .x5 2], guard (.ltu .x5 .x12) 8,
  b [.SUB .x5 .x5 .x12], guard (.ltu .x5 .x13) 8,
  b [.ADD .x16 .x12 .x13, .ADDI .x5 .x0 1], guard (.ltu .x5 .x14)]

/-- One explicit in-flight plaintext borrow per stream. Core can copy into its
own immutable datagram and settle before reserving another stream range. -/
def reserve : SAsm.Stmt := seq [sendState, rangeEnd,
  guard (.ne .x26 .x0) 9, guard (.ne .x27 .x0) 8,
  guard (.ltu .x12 .x20) 8, guard (.ltu .x22 .x12) 8, guard (.ltu .x21 .x16) 8,
  .ite (.ne .x14 .x0) (guard (.ne .x25 .x16) 4) nil,
  b [.ADDI .x11 .x0 0],
  .ite (.ltu .x22 .x16) (b [.SUB .x11 .x16 .x22]) nil,
  guard (.ltu .x23 .x16) 3, guard (.ltu .x24 .x11) 3,
  b [.SD .x8 .x12 96, .SD .x8 .x13 104, .SD .x8 .x14 112,
    .ADDI .x5 .x0 1, .SD .x8 .x5 120,
    .REMU .x12 .x12 .x9, .SUB .x5 .x9 .x12, .ADDI .x14 .x0 0],
  .ite (.ltu .x5 .x13) (b [.SUB .x14 .x13 .x5, .ADDI .x13 .x5 0]) nil,
  b [.ADDI .x10 .x0 0], exit true]

/-- Frees only the contiguous ACK prefix, never a pending borrowed byte. -/
private def collect : SAsm.Stmt := seq [
  b [.ADDI .x5 .x20 0], .loop (.ltu .x5 .x22) (seq [
    b [.LD .x6 .x8 120, .LD .x7 .x8 96],
    .ite (.ne .x6 .x0) (.ite (.geu .x5 .x7)
      (b [.ADDI .x22 .x5 0]) nil) nil,
    .ite (.ltu .x5 .x22) (seq [
      b [.REMU .x6 .x5 .x9, .ADD .x7 .x19 .x6, .LBU .x28 .x7 0],
      .ite (.eq .x28 .x0) (b [.ADDI .x22 .x5 0])
        (b [.SB .x7 .x0 0, .ADD .x7 .x18 .x6, .SB .x7 .x0 0,
          .ADDI .x5 .x5 1])]) nil]), b [.SD .x8 .x5 24]]

/-- a2=0 cancel (releases reservation) / 1 SendResult success (commits it).
Both return a1=reserved new-byte delta. Would-block must NOT call settle. -/
def settle : SAsm.Stmt := seq [sendState,
  b [.ADDI .x5 .x0 1], guard (.ltu .x5 .x12), guard (.eq .x27 .x0) 8,
  b [.LD .x5 .x8 96, .LD .x6 .x8 104, .LD .x7 .x8 112,
    .ADDI .x11 .x0 0],
  guard (.ltu .x5 .x20), guard (.ltu .x22 .x5),
  b [.SUB .x16 .x21 .x5], guard (.ltu .x16 .x6),
  b [.ADD .x16 .x5 .x6, .ADDI .x5 .x0 1], guard (.ltu .x5 .x7),
  .ite (.ne .x7 .x0) (guard (.ne .x25 .x16) 4) nil,
  .ite (.ltu .x22 .x16) (b [.SUB .x11 .x16 .x22]) nil,
  .ite (.ne .x12 .x0) (seq [
    .ite (.ltu .x22 .x16) (b [.ADDI .x22 .x16 0, .SD .x8 .x22 40]) nil,
    .ite (.ne .x7 .x0) (b [.SD .x8 .x7 72]) nil]) nil,
  b [.SD .x8 .x0 96, .SD .x8 .x0 104, .SD .x8 .x0 112, .SD .x8 .x0 120,
    .ADDI .x14 .x12 0], collect,
  b [.ADDI .x10 .x0 0, .ADDI .x12 .x0 0, .ADDI .x13 .x0 0], exit true]

/-- a2/a3 ACK range, a4 FIN acknowledged. Caller proves range belongs to a
successfully sent PN, checks packet authentication, and handles recovery metadata. -/
def acknowledge : SAsm.Stmt := seq [sendState, rangeEnd,
  guard (.ltu .x22 .x16) 8,
  .ite (.ne .x14 .x0) (seq [b [.LD .x5 .x8 72],
    guard (.eq .x5 .x0) 4, guard (.ne .x25 .x16) 4]) nil,
  .ite (.ltu .x12 .x20) (b [.ADDI .x12 .x20 0]) nil,
  .loop (.ltu .x12 .x16) (b [.REMU .x5 .x12 .x9,
    .ADD .x5 .x19 .x5, .ADDI .x6 .x0 1, .SB .x5 .x6 0, .ADDI .x12 .x12 1]),
  .ite (.ne .x14 .x0) (b [.SD .x8 .x14 80]) nil,
  collect, zeroOutputs, b [.LD .x5 .x8 24, .SUB .x11 .x5 .x20], exit true]

/-- Local reset and STOP_SENDING response. Resolve outstanding SendResult before
calling; no borrowed bytes are invalidated. Final size equals committed sent end. -/
def stop : SAsm.Stmt := seq [sendState, guard (.ne .x27 .x0) 8,
  b [.ADDI .x5 .x0 0], .loop (.ltu .x5 .x9) (b [
    .ADD .x6 .x18 .x5, .SB .x6 .x0 0, .ADD .x6 .x19 .x5, .SB .x6 .x0 0,
    .ADDI .x5 .x5 1]), b [.SD .x8 .x22 24, .SD .x8 .x22 32,
    .SD .x8 .x22 64, .ADDI .x5 .x0 1, .SD .x8 .x5 88],
  zeroOutputs, b [.ADDI .x14 .x0 2], exit true]

end Libp2pAsm.Asm.Stream
