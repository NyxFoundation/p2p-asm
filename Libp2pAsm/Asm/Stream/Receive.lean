import Libp2pAsm.Asm.Stream.Common

namespace Libp2pAsm.Asm.Stream
open Rv64 Crypto.Util

/-- 80-byte state. See Tests/Streams/README.md for exact LE64 ABI and ownership. -/
def receiveState : SAsm.Stmt := seq [preflight 80, b [
  .LD .x9 .x8 0, .LD .x18 .x8 8, .LD .x19 .x8 16,
  .LD .x20 .x8 24, .LD .x21 .x8 32, .LD .x22 .x8 40,
  .LD .x23 .x8 48, .LD .x24 .x8 56, .LD .x25 .x8 64, .LD .x26 .x8 72,
  .ADDI .x7 .x0 (-1), .SRLI .x7 .x7 2],
  guard (.eq .x9 .x0), guard (.ltu .x7 .x9),
  guard (.ltu .x21 .x20), guard (.ltu .x7 .x21),
  guard (.ltu .x7 .x23), guard (.ltu .x7 .x24),
  b [.ADDI .x5 .x0 1], guard (.ltu .x5 .x25), guard (.ltu .x5 .x26),
  b [.ADDI .x5 .x0 (-1)],
  .ite (.ne .x22 .x5) (seq [guard (.ltu .x7 .x22), guard (.ltu .x22 .x21)]) nil,
  .ite (.ne .x26 .x0) (guard (.eq .x22 .x5)) nil,
  span .x18 .x9, span .x19 .x9]

private def receiveChecks : SAsm.Stmt := seq [
  sourceView, b [.ADDI .x5 .x0 2], guard (.ltu .x5 .x17),
  .ite (.ne .x25 .x0) (guard (.ne .x17 .x0)) nil,
  .ite (.eq .x17 .x5) (guard (.ne .x15 .x0)) nil,
  b [.ADDI .x7 .x0 (-1), .SRLI .x7 .x7 2],
  guard (.ltu .x7 .x16) 2, b [.SUB .x5 .x7 .x16], guard (.ltu .x5 .x15) 2,
  b [.ADD .x27 .x16 .x15, .ADDI .x5 .x0 (-1)],
  .ite (.ne .x22 .x5) (seq [guard (.ltu .x22 .x27) 4,
    .ite (.ne .x17 .x0) (guard (.ne .x22 .x27) 4) nil]) nil,
  .ite (.ne .x17 .x0) (guard (.ltu .x27 .x21) 4) nil,
  b [.ADDI .x11 .x0 0],
  .ite (.ltu .x21 .x27) (b [.SUB .x11 .x27 .x21]) nil,
  .ite (.eq .x25 .x0) (seq [guard (.ltu .x23 .x27) 3,
    guard (.ltu .x24 .x11) 3]) (b [.ADDI .x11 .x0 0])]

/-- Conflict scan accumulates XOR, branching only on the released conflict result.
Bytes below consumed are retired and ignored, as allowed by RFC9000 §2.2. -/
private def scan (publish : Bool) : SAsm.Stmt := seq [
  b [.ADDI .x5 .x16 0, .ADDI .x6 .x12 0, .ADDI .x30 .x0 0],
  .loop (.ltu .x5 .x27) (seq [
    .ite (.geu .x5 .x20) (seq [b [.REMU .x7 .x5 .x9,
      .ADD .x28 .x19 .x7, .ADD .x29 .x18 .x7, .LBU .x7 .x6 0],
      if publish then b [.SB .x29 .x7 0, .ADDI .x7 .x0 1, .SB .x28 .x7 0]
      else seq [b [.LBU .x28 .x28 0], .ite (.ne .x28 .x0)
        (b [.LBU .x29 .x29 0, .XOR .x29 .x29 .x7, .OR .x30 .x30 .x29]) nil]]) nil,
    b [.ADDI .x5 .x5 1, .ADDI .x6 .x6 1]])]

private def bufferData : SAsm.Stmt := seq [
  .ite (.ne .x15 .x0) (.ite (.ltu .x20 .x27) (seq [
    b [.SUB .x5 .x27 .x20], .ite (.ltu .x9 .x5)
      (.ite (.eq .x25 .x0) (fail 6) (fail 7)) nil]) nil) nil,
  scan false, guard (.ne .x30 .x0) 5, scan true]

private def resetData : SAsm.Stmt := seq [
  b [.ADDI .x5 .x0 0], .loop (.ltu .x5 .x9) (b [
    .ADD .x6 .x18 .x5, .SB .x6 .x0 0, .ADD .x6 .x19 .x5, .SB .x6 .x0 0,
    .ADDI .x5 .x5 1]), b [.ADDI .x26 .x0 1, .SD .x8 .x26 72]]

/-- a0/a1 state/capacity; a2..a5 source view; a6 stream offset; a7=0/FIN/RESET.
Allowance is caller supplied at state+56. Success a1 is exact connection delta.
Every content failure preserves all state/storage. -/
def receive : SAsm.Stmt := seq [receiveState, receiveChecks,
  b [.ADDI .x5 .x0 2], .ite (.eq .x17 .x5) resetData
    (.ite (.eq .x26 .x0) bufferData nil),
  .ite (.ltu .x21 .x27) (b [.SD .x8 .x27 32]) nil,
  .ite (.ne .x17 .x0) (b [.SD .x8 .x27 40]) nil,
  b [.ADDI .x10 .x0 0, .ADDI .x12 .x0 0, .ADDI .x13 .x0 0,
    .ADDI .x14 .x17 0], exit true]

/-- Returns a2=ring-relative offset and a3=contiguous length, never a host pointer.
One view stops at wrap. a4=1 iff all bytes through final size were consumed,
2 iff reset. These are uncommitted outputs until the caller's auth gate. -/
def peek : SAsm.Stmt := seq [receiveState, zeroOutputs,
  b [.REMU .x12 .x20 .x9, .SUB .x6 .x9 .x12],
  .ite (.eq .x20 .x22) (b [.ADDI .x14 .x0 1]) nil,
  .ite (.ne .x26 .x0) (b [.ADDI .x14 .x0 2]) nil,
  .ite (.eq .x26 .x0) (.loop (.ltu .x13 .x6) (seq [
    b [.ADD .x7 .x12 .x13, .ADD .x7 .x19 .x7, .LBU .x7 .x7 0],
    .ite (.eq .x7 .x0) (exit true) nil,
    b [.ADDI .x13 .x13 1]])) nil,
  .ite (.eq .x20 .x22) (b [.ADDI .x14 .x0 1]) nil,
  .ite (.ne .x26 .x0) (b [.ADDI .x14 .x0 2]) nil, exit true]

/-- a2 byte count; validates the entire consumed range before wiping it. -/
def consume : SAsm.Stmt := seq [receiveState,
  guard (.ltu .x9 .x12) 8, b [.SUB .x5 .x21 .x20], guard (.ltu .x5 .x12) 8,
  b [.ADDI .x5 .x0 0], .loop (.ltu .x5 .x12) (seq [
    b [.ADD .x6 .x20 .x5, .REMU .x6 .x6 .x9, .ADD .x7 .x19 .x6,
      .LBU .x7 .x7 0], guard (.eq .x7 .x0) 8, b [.ADDI .x5 .x5 1]]),
  b [.ADDI .x5 .x0 0], .loop (.ltu .x5 .x12) (b [
    .ADD .x6 .x20 .x5, .REMU .x6 .x6 .x9, .ADD .x7 .x19 .x6,
    .SB .x7 .x0 0, .ADD .x7 .x18 .x6, .SB .x7 .x0 0, .ADDI .x5 .x5 1]),
  b [.ADD .x20 .x20 .x12, .SD .x8 .x20 24], zeroOutputs, exit true]

end Libp2pAsm.Asm.Stream
