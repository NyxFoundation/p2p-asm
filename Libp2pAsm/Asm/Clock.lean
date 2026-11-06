import Libp2pAsm.Asm.Basic

namespace Libp2pAsm.Asm

open Rv64

private def billion : SAsm.Stmt :=
  .block [.LUI .x17 (BitVec.ofNat 20 ((1000000000 + 2048) / 4096)),
    .ADDI .x17 .x17 (BitVec.ofInt 12 (-1536))]

private def finish (status : BitVec 12) : SAsm.Stmt := returnError status

private def trusted : SAsm.Stmt :=
  sequence [.block [.ADDI .x16 .x0 1, .SD .x5 .x16 0], finish 0]

private def stop : SAsm.Stmt :=
  sequence [.block [.ADDI .x16 .x0 3, .SD .x5 .x16 0,
    .SD .x5 .x0 16, .SD .x5 .x0 24], finish 2]

private def unavailable : SAsm.Stmt :=
  sequence [.block [.ADDI .x16 .x0 2, .SD .x5 .x16 0,
    .SD .x5 .x31 8, .SD .x5 .x0 16, .SD .x5 .x0 24], finish 1]

private def checkState : SAsm.Stmt :=
  sequence [
    rejectIf (.eq .x12 .x0) 3, rejectIf (.eq .x13 .x0) 3,
    rejectIf (.ltu .x12 .x13) 3,
    .block [.ADDI .x5 .x10 0, .LD .x6 .x5 0, .ADDI .x16 .x0 4],
    rejectIf (.ltu .x16 .x6) 4,
    .block [.LD .x7 .x5 8, .LD .x28 .x5 16, .LD .x29 .x5 24], billion,
    .ite (.eq .x6 .x16) (rejectIf (.geu .x29 .x17) 4) (.block []),
    .block [.ADDI .x16 .x0 1],
    .ite (.eq .x6 .x16) (rejectIf (.geu .x29 .x17) 4) (.block []),
    .block [.ADDI .x16 .x0 3],
    .ite (.eq .x6 .x16) (finish 2) (.block [])]

private def checkSample : SAsm.Stmt :=
  sequence [
    .block [.LD .x16 .x11 0, .LD .x30 .x11 8, .LD .x31 .x11 16,
      .ADDI .x10 .x0 2],
    .ite (.geu .x16 .x10) stop (.block []),
    .ite (.ltu .x31 .x30) stop (.block []),
    .ite (.ne .x6 .x0) (.ite (.ltu .x30 .x7) stop (.block [])) (.block []),
    .ite (.ne .x16 .x0) unavailable (.block []),
    .block [.SUB .x10 .x31 .x30],
    .ite (.ltu .x13 .x10) unavailable (.block []),
    .block [.LD .x14 .x11 24, .LD .x15 .x11 32],
    .ite (.geu .x15 .x17) unavailable (.block [])]

/-- Form the exact nonnegative elapsed wall duration in x28:x29.
    Both seconds are signed words; their nonnegative difference fits an unsigned word.
    Multiplication and nanosecond carry retain the full 128-bit result. -/
private def elapsed : SAsm.Stmt :=
  sequence [
    .block [.SLT .x16 .x14 .x28], rejectIf (.ne .x16 .x0) 1,
    .ite (.eq .x14 .x28) (rejectIf (.ltu .x15 .x29) 1) (.block []),
    .block [.SUB .x30 .x14 .x28],
    .ite (.ltu .x15 .x29)
      (.block [.ADDI .x30 .x30 (BitVec.ofInt 12 (-1)),
        .ADD .x16 .x15 .x17, .SUB .x16 .x16 .x29])
      (.block [.SUB .x16 .x15 .x29]),
    .block [.MULHU .x28 .x30 .x17, .MUL .x30 .x30 .x17,
      .ADD .x29 .x30 .x16, .SLTU .x16 .x29 .x30, .ADD .x28 .x28 .x16,
      .SUB .x11 .x31 .x7]]

private def checkDifference : SAsm.Stmt :=
  sequence [
    .ite (.eq .x28 .x0)
      (.ite (.ltu .x29 .x11) (.block [.SUB .x29 .x11 .x29])
        (.block [.SUB .x29 .x29 .x11]))
      (sequence [.block [.SLTU .x16 .x29 .x11, .SUB .x28 .x28 .x16,
          .SUB .x29 .x29 .x11], rejectIf (.ne .x28 .x0) 1]),
    rejectIf (.ltu .x12 .x29) 1, trusted]

/-- a0=32-byte state, a1=40-byte sample, a2=drift ns, a3=max sample span ns.
    State: mode/previous mono-after/signed UTC seconds/nanoseconds.
    Sample: source status/mono-before/mono-after/signed UTC seconds/nanoseconds.
    All fields are LE64, ranges are disjoint/8-aligned, state writable, sample readable.
    Statuses match Spec.Clock; no stack or callee-saved registers are used.
    Correlation/order of samples and cleanup of affected connections belong to the caller. -/
def checkClock : SAsm.Stmt :=
  sequence [checkState, checkSample,
    .block [.ADDI .x16 .x0 4, .SD .x5 .x16 0, .SD .x5 .x31 8,
      .SD .x5 .x14 16, .SD .x5 .x15 24, .ADDI .x16 .x0 2],
    .ite (.eq .x6 .x16) (finish 1) (.block []),
    .ite (.eq .x6 .x0) trusted (.block []),
    elapsed, checkDifference]

end Libp2pAsm.Asm
