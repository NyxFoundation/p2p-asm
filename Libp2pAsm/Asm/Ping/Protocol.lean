import Libp2pAsm.Asm.Stream.Common

namespace Libp2pAsm.Asm.Ping
open Rv64 Crypto.Util Libp2pAsm.Asm.Stream

private def state : SAsm.Stmt := seq [preflight 128, b [
  .LD .x9 .x8 0, .LD .x18 .x8 8, .LD .x19 .x8 16, .LD .x20 .x8 24,
  .LD .x21 .x8 32, .LD .x22 .x8 40, .LD .x23 .x8 48, .LD .x24 .x8 56,
  .ADDI .x5 .x0 1], guard (.ltu .x5 .x9),
  guard (.ltu .x5 .x22), guard (.ltu .x5 .x23),
  b [.ADDI .x5 .x0 3], guard (.ltu .x5 .x18), guard (.ltu .x5 .x21),
  b [.ADDI .x5 .x0 32], guard (.ltu .x5 .x19)]

private def gate : SAsm.Stmt := seq [b [.ADDI .x5 .x0 3], guard (.ne .x21 .x5) 11]

/-- EntropyReady token/length are checked. Bytes must come from the caller's
OS-entropy completion, never a packet, fixed seed or a runtime fallback. -/
def begin : SAsm.Stmt := seq [state, gate, sourceView,
  guard (.geu .x16 .x20) 10, b [.ADDI .x5 .x0 32], guard (.ne .x15 .x5),
  guard (.ne .x17 .x24), guard (.ne .x9 .x0),
  guard (.ne .x18 .x0) 9, guard (.ne .x22 .x0) 9, guard (.ne .x23 .x0) 9,
  b [.ADDI .x5 .x0 0], .loop (.ltu .x5 .x15) (b [
    .ADD .x6 .x12 .x5, .LBU .x6 .x6 0, .ADD .x7 .x8 .x5, .SB .x7 .x6 96,
    .ADDI .x5 .x5 1]), b [.ADDI .x5 .x0 1, .SD .x8 .x5 8],
  zeroOutputs, b [.ADDI .x12 .x0 96, .ADDI .x13 .x0 32, .ADDI .x14 .x0 1], exit true]

private def checkResponse : SAsm.Stmt := seq [
  b [.ADDI .x5 .x0 0, .ADDI .x28 .x0 0, .ADDI .x29 .x0 32],
  .loop (.ltu .x5 .x29) (seq [
    .ite (.ltu .x5 .x19) (b [.ADD .x6 .x8 .x5, .LBU .x6 .x6 64])
      (b [.SUB .x6 .x5 .x19, .ADD .x6 .x12 .x6, .LBU .x6 .x6 0]),
    b [.ADD .x7 .x8 .x5, .LBU .x7 .x7 96, .XOR .x6 .x6 .x7,
      .OR .x28 .x28 .x6, .ADDI .x5 .x5 1]]), guard (.ne .x28 .x0) 12]

private def receiveChecks : SAsm.Stmt := seq [state, gate, sourceView,
  guard (.geu .x16 .x20) 10, b [.ADDI .x5 .x0 1], guard (.ltu .x5 .x17),
  b [.ADDI .x5 .x0 3], guard (.eq .x18 .x5) 9, guard (.ne .x23 .x0) 9,
  .ite (.ne .x9 .x0) (guard (.ne .x22 .x0) 9) nil,
  b [.ADDI .x5 .x0 2], guard (.eq .x18 .x5) 8,
  .ite (.eq .x9 .x0) (seq [b [.ADDI .x5 .x0 1], guard (.ne .x18 .x5) 8]) nil,
  b [.ADDI .x25 .x0 32, .SUB .x25 .x25 .x19],
  .ite (.ltu .x15 .x25) (b [.ADDI .x25 .x15 0]) nil,
  b [.ADD .x26 .x19 .x25, .ADDI .x27 .x0 0],
  .ite (.eq .x25 .x15) (b [.ADDI .x27 .x17 0]) nil,
  .ite (.ne .x27 .x0) (.ite (.ne .x26 .x0) (seq [
    b [.ADDI .x5 .x0 32], guard (.ne .x26 .x5) 13]) nil) nil,
  .ite (.ne .x27 .x0) (.ite (.eq .x26 .x0)
    (.ite (.eq .x9 .x0) (fail 13) nil) nil) nil,
  b [.ADDI .x5 .x0 32], .ite (.eq .x26 .x5)
    (.ite (.eq .x9 .x0) checkResponse nil) nil]

/-- Processes at most one 32-byte message, returning a1 consumed bytes. FIN is
applied only if the entire supplied view was consumed. Ready views are owned
state-relative offsets, immutable until release/cancel. -/
def feed : SAsm.Stmt := seq [receiveChecks,
  b [.ADDI .x5 .x0 0, .ADD .x29 .x8 .x19],
  .loop (.ltu .x5 .x25) (b [.ADD .x6 .x12 .x5, .LBU .x6 .x6 0,
    .ADD .x7 .x29 .x5, .SB .x7 .x6 64, .ADDI .x5 .x5 1]),
  b [.SD .x8 .x26 16, .SD .x8 .x27 48], zeroOutputs,
  b [.ADDI .x11 .x25 0, .ADDI .x5 .x0 32],
  .ite (.eq .x26 .x5) (seq [b [.ADDI .x5 .x0 2, .SD .x8 .x5 8],
    .ite (.eq .x9 .x0) (b [.ADDI .x14 .x0 2])
      (b [.ADDI .x12 .x0 64, .ADDI .x13 .x0 32, .ADDI .x14 .x0 1])]) nil,
  .ite (.eq .x26 .x0) (.ite (.ne .x27 .x0) (b [
    .ADDI .x5 .x0 3, .SD .x8 .x5 8, .ADDI .x5 .x0 1, .SD .x8 .x5 40,
    .ADDI .x14 .x0 3]) nil) nil, exit true]

private def wipePayload : SAsm.Stmt := seq [b [.ADDI .x5 .x0 0, .ADDI .x6 .x0 64],
  .loop (.ltu .x5 .x6) (b [.ADD .x7 .x8 .x5, .SB .x7 .x0 64, .ADDI .x5 .x5 1]),
  b [.SD .x8 .x0 16]]

/-- Caller invokes after copying echo to its send buffer or committing the match
notification. It must not release while a returned view remains borrowed. -/
def release : SAsm.Stmt := seq [state, gate, guard (.geu .x12 .x20) 10,
  b [.ADDI .x5 .x0 2], guard (.ne .x18 .x5) 8,
  wipePayload, zeroOutputs,
  .ite (.eq .x9 .x0) (b [.ADDI .x5 .x22 0, .ADDI .x14 .x0 1])
    (b [.ADDI .x5 .x23 0]),
  .ite (.ne .x5 .x0) (b [.ADDI .x5 .x0 3, .SD .x8 .x5 8,
    .ADDI .x5 .x0 1, .SD .x8 .x5 40, .ADDI .x14 .x0 3])
    (b [.SD .x8 .x0 8]), exit true]

/-- Half-close send direction; an outstanding outbound reply remains receivable. -/
def finish : SAsm.Stmt := seq [state, gate,
  .ite (.ne .x9 .x0) (seq [b [.ADDI .x5 .x0 2], guard (.eq .x18 .x5) 8]) nil,
  b [.ADDI .x5 .x0 3], guard (.eq .x18 .x5) 9,
  b [.ADDI .x5 .x0 1, .SD .x8 .x5 40], zeroOutputs,
  b [.ADDI .x14 .x0 3], exit true]

/-- Cancellation/timeout revoke application state; caller first resolves borrows.
Timers on an already closed state and early timers are idempotent no-ops. -/
def cancel (timer : Bool := false) : SAsm.Stmt := seq [state,
  if timer then seq [b [.ADDI .x5 .x0 3],
    .ite (.eq .x18 .x5) (seq [zeroOutputs, exit true]) nil,
    .ite (.ltu .x12 .x20) (seq [zeroOutputs, exit true]) nil] else nil,
  wipePayload, b [.ADDI .x5 .x0 3, .SD .x8 .x5 8,
    .ADDI .x5 .x0 1, .SD .x8 .x5 40], zeroOutputs,
  b [.ADDI .x14 .x0 (if timer then 5 else 4)], exit true]

/-- Per-peer two-word counters. a2=role, a3=0 release/1 acquire. Caller owns
stream-handle generation and invokes exactly once per allocation/release. -/
def quota : SAsm.Stmt := seq [preflight 16,
  b [.ADDI .x5 .x0 1], guard (.ltu .x5 .x12), guard (.ltu .x5 .x13),
  b [.LD .x6 .x8 0], guard (.ltu .x5 .x6), b [.LD .x6 .x8 8, .ADDI .x5 .x0 2],
  guard (.ltu .x5 .x6), b [.SLLI .x7 .x12 3, .ADD .x7 .x8 .x7,
    .LD .x6 .x7 0, .ADDI .x5 .x12 1],
  .ite (.eq .x13 .x0) (seq [guard (.eq .x6 .x0) 8, b [.ADDI .x6 .x6 (-1)]])
    (seq [guard (.geu .x6 .x5) 8, b [.ADDI .x6 .x6 1]]),
  b [.SD .x7 .x6 0], zeroOutputs, b [.ADDI .x11 .x6 0], exit true]

end Libp2pAsm.Asm.Ping
