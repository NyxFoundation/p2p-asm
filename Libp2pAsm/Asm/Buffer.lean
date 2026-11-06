import Libp2pAsm.Asm.Basic

namespace Libp2pAsm.Asm

open Rv64

private def lookupRegion : SAsm.Stmt :=
  sequence [
    .block [.ADDI .x6 .x0 1], rejectIf (.ltu .x6 .x13) 4,
    .block [.SRLI .x6 .x12 59], rejectIf (.ne .x6 .x0) 4,
    .block [.LD .x5 .x11 0], rejectIf (.geu .x5 .x12) 1,
    .block [.SLLI .x6 .x5 5, .ADD .x7 .x10 .x6], rejectIf (.ltu .x7 .x10) 4,
    .block [.LD .x5 .x7 24, .SRLI .x6 .x5 2], rejectIf (.ne .x6 .x0) 4,
    .block [.ANDI .x6 .x5 1], rejectIf (.eq .x6 .x0) 2,
    .block [.LD .x6 .x7 0, .LD .x28 .x11 8], rejectIf (.ne .x6 .x28) 2]

private def validateRegion : SAsm.Stmt :=
  sequence [
    .block [.LD .x30 .x7 16, .LD .x28 .x7 8], rejectIf (.eq .x30 .x0) 4,
    .block [.ADD .x29 .x28 .x30], rejectIf (.ltu .x29 .x28) 4,
    .ite (.ne .x13 .x0)
      (sequence [.block [.ANDI .x5 .x5 2], rejectIf (.eq .x5 .x0) 5])
      (.block [])]

/-- a0=region table, a1=32-byte reference, a2=region count, a3=write (0/1).
    A slot is (generation, base, capacity, flags) as four LE64 fields.
    A reference is (slot, generation, offset, length) as four LE64 fields.
    Table and reference memory are owned, readable, and 8-byte aligned on entry.
    The core-owned registry already establishes mapping, ownership and code separation;
    these descriptors are not accepted directly from network input.
    Return a0=status, a1=address, a2=length; errors zero both result fields. -/
def resolveBuffer : SAsm.Stmt :=
  sequence [
    lookupRegion, validateRegion,
    .block [.LD .x6 .x11 24, .LD .x5 .x11 16], rejectIf (.ltu .x30 .x6) 3,
    .block [.SUB .x7 .x30 .x6], rejectIf (.ltu .x7 .x5) 3,
    .block [.ADD .x28 .x28 .x5, .ADDI .x11 .x28 0,
      .ADDI .x12 .x6 0, .ADDI .x10 .x0 0], .ret]

end Libp2pAsm.Asm
