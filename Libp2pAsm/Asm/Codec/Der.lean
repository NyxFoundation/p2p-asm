import Libp2pAsm.Asm.Crypto.Util

namespace Libp2pAsm.Asm.Codec.Der
open Rv64 Crypto.Util

private def success (outputs : List Reg) : SAsm.Stmt := sequence [
  block ((Crypto.Sha2.cleared.filter (fun r => !outputs.contains r)).map
    fun r => .ADDI r .x0 0), .ret]

private def tagCheck (r : Reg) : SAsm.Stmt := sequence [
  block [.SRLI .x5 r 8], reject (.ne .x5 .x0) 6,
  block [.ANDI .x5 r 31, .ADDI .x6 .x0 31], reject (.eq .x5 .x6) 6,
  block [.ANDI .x5 r (-33)], reject (.eq .x5 .x0) 6]

private def longLength : SAsm.Stmt := sequence [
  block [.ADDI .x7 .x0 128], reject (.eq .x13 .x7) 7,
  block [.ADDI .x7 .x0 255], reject (.eq .x13 .x7) 8,
  block [.ANDI .x17 .x13 127, .ADDI .x7 .x0 8], reject (.ltu .x7 .x17) 2,
  reject (.ltu .x16 .x17) 1,
  block [.LBU .x5 .x15 0], reject (.eq .x5 .x0) 3,
  block [.ADDI .x13 .x0 0, .ADD .x14 .x14 .x17, .SUB .x16 .x16 .x17],
  .loop (.ne .x17 .x0) (block [
    .LBU .x5 .x15 0, .SLLI .x13 .x13 8, .OR .x13 .x13 .x5,
    .ADDI .x15 .x15 1, .ADDI .x17 .x17 (-1)]),
  block [.ADDI .x7 .x0 128], reject (.ltu .x13 .x7) 3]

/-- a0=input,a1=available. Returns a0=status; on success a1=tag,a2=header bytes,
a3=content bytes,a4=total consumed. Failure clears all four results.
Read-only, no stack; all other caller-saved registers are cleared. Mapping/code
separation are caller preconditions; checked accessed span is nonwrapping.
Only header bytes (at most ten) are read, but the entire content must be present. -/
def decode : SAsm.Stmt := sequence [
  range .x10 .x11, reject (.eq .x11 .x0) 1,
  block [.LBU .x12 .x10 0], tagCheck .x12,
  block [.ADDI .x7 .x0 2], reject (.ltu .x11 .x7) 1,
  block [.LBU .x13 .x10 1, .ADDI .x14 .x0 2, .ADDI .x15 .x10 2,
    .ADDI .x16 .x11 (-2), .ANDI .x5 .x13 128],
  .ite (.ne .x5 .x0) longLength empty,
  reject (.ltu .x16 .x13) 1,
  block [.ADDI .x11 .x12 0, .ADDI .x12 .x14 0, .ADD .x14 .x14 .x13],
  success [.x11, .x12, .x13, .x14]]

private def countLength : SAsm.Stmt := sequence [
  block [.ADDI .x28 .x11 0, .ADDI .x29 .x0 0],
  .loop (.ne .x28 .x0) (block [.SRLI .x28 .x28 8, .ADDI .x29 .x29 1]),
  block [.ADDI .x31 .x29 2]]

private def writeLong : SAsm.Stmt := sequence [
  block [.ORI .x5 .x29 128, .SB .x12 .x5 1,
    .ADDI .x30 .x31 (-1), .ADD .x30 .x12 .x30],
  .loop (.ne .x29 .x0) (block [.SB .x30 .x11 0,
    .SRLI .x11 .x11 8, .ADDI .x30 .x30 (-1), .ADDI .x29 .x29 (-1)])]

/-- a0=tag,a1=content length,a2=header output,a3=capacity. Returns a0=status,
a1=written header length. Does not allocate, read or write the content.
Capacity/range/tag failures have no memory access. Writes at most ten bytes.
Preserves ra/sp/gp/tp/s-registers; other caller-saved registers are cleared. -/
def encodeHeader : SAsm.Stmt := sequence [
  tagCheck .x10,
  block [.ADDI .x7 .x0 128, .ADDI .x31 .x0 2],
  .ite (.geu .x11 .x7) countLength empty,
  reject (.ltu .x13 .x31) 5, range .x12 .x31,
  block [.SB .x12 .x10 0, .ADDI .x7 .x0 2],
  .ite (.eq .x31 .x7) (block [.SB .x12 .x11 1]) writeLong,
  block [.ADDI .x11 .x31 0], success [.x11]]

end Libp2pAsm.Asm.Codec.Der
