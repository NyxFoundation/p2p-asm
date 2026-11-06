import Libp2pAsm.Asm.Crypto.Util

namespace Libp2pAsm.Asm.Identity.Time
open Rv64 Crypto.Util

private def success : SAsm.Stmt := sequence [
  block ((Crypto.Sha2.cleared.filter (· != .x11)).map fun r => .ADDI r .x0 0), .ret]

/-- Public calendar arithmetic. Clobbers t0/t1/t2, never the year. -/
private def leap (year out : Reg) : SAsm.Stmt := sequence [
  block [.ADDI out .x0 0, .ADDI .x7 .x0 4, .REMU .x5 year .x7],
  .ite (.eq .x5 .x0) (sequence [
    block [.ADDI out .x0 1, .ADDI .x7 .x0 100, .REMU .x5 year .x7],
    .ite (.eq .x5 .x0) (sequence [
      block [.ADDI .x7 .x0 400, .REMU .x5 year .x7,
        .SLTU out .x0 .x5, .XORI out out 1]]) empty]) empty]

/-- Year1 has day index0. out/tmp/year must be distinct, none t0/t2. -/
private def beforeYear (year out tmp : Reg) : SAsm.Stmt := block [
  .ADDI .x5 year (-1), .ADDI .x7 .x0 365, .MUL out .x5 .x7,
  .SRLI tmp .x5 2, .ADD out out tmp,
  .ADDI .x7 .x0 100, .DIVU tmp .x5 .x7, .SUB out out tmp,
  .ADDI .x7 .x0 400, .DIVU tmp .x5 .x7, .ADD out out tmp]

private def beforeMonth (month isLeap out : Reg) : SAsm.Stmt := sequence [
  block [.ADDI .x7 .x0 367, .MUL out month .x7, .ADDI out out (-362),
    .ADDI .x7 .x0 12, .DIVU out out .x7, .ADDI .x7 .x0 2],
  .ite (.ltu .x7 month) (block [.ADDI out out (-2), .ADD out out isLeap]) empty]

private def monthDays : SAsm.Stmt := sequence (
  [block [.ADDI .x30 .x0 31]] ++
  ([4, 6, 9, 11].map fun m => sequence [block [.ADDI .x7 .x0 (imm m)],
    .ite (.eq .x14 .x7) (block [.ADDI .x30 .x0 30]) empty]) ++
  [block [.ADDI .x7 .x0 2],
    .ite (.eq .x14 .x7) (block [.ADDI .x30 .x29 28]) empty])

private def readDigits (dst : Reg) (start count : Nat) : SAsm.Stmt := sequence (
  [block [.ADDI dst .x0 0]] ++ (List.range count).map fun i => sequence [
    block [.LBU .x5 .x11 (imm (start+i)), .ADDI .x5 .x5 (-48), .ADDI .x7 .x0 10],
    reject (.geu .x5 .x7) 6,
    block [.MUL dst dst .x7, .ADD dst dst .x5]])

private def readFields (width : Nat) : SAsm.Stmt := sequence [
  block [.LBU .x5 .x11 (imm (width+10)), .ADDI .x7 .x0 90],
  reject (.ne .x5 .x7) 6, readDigits .x13 0 width,
  if width == 2 then sequence [block [.ADDI .x7 .x0 50],
    .ite (.ltu .x13 .x7) (block [.ADDI .x13 .x13 2000])
      (block [.ADDI .x13 .x13 1900])] else empty,
  readDigits .x14 width 2, readDigits .x15 (width+2) 2,
  readDigits .x16 (width+4) 2, readDigits .x17 (width+6) 2,
  readDigits .x28 (width+8) 2]

private def validFields : SAsm.Stmt := sequence [
  reject (.eq .x13 .x0) 6,
  block [.ADDI .x5 .x14 (-1), .ADDI .x7 .x0 12], reject (.geu .x5 .x7) 6,
  leap .x13 .x29, monthDays,
  reject (.eq .x15 .x0) 6, reject (.ltu .x30 .x15) 6,
  block [.ADDI .x7 .x0 24], reject (.geu .x16 .x7) 6,
  block [.ADDI .x7 .x0 60], reject (.geu .x17 .x7) 6,
  reject (.geu .x28 .x7) 6]

private def seconds : SAsm.Stmt := sequence [
  beforeYear .x13 .x30 .x31, beforeMonth .x14 .x29 .x31,
  block ([.ADD .x30 .x30 .x31, .ADD .x30 .x30 .x15, .ADDI .x30 .x30 (-1)] ++
    load .x7 719162 ++ [.SUB .x30 .x30 .x7] ++ load .x7 86400 ++
    [.MUL .x30 .x30 .x7] ++ load .x7 3600 ++
    [.MUL .x16 .x16 .x7, .ADD .x30 .x30 .x16, .ADDI .x7 .x0 60,
      .MUL .x17 .x17 .x7, .ADD .x30 .x30 .x17, .ADD .x11 .x30 .x28]), success]

/-- a0=ASN.1 tag(23/24),a1=body,a2=body length(13/15).
Returns a0=status,a1=signed Unix seconds; failures clear a1.
No stack, allocation or writes. ASCII/calendar checks never normalize malformed
dates. Mapping/permissions/code separation are caller preconditions. -/
def decode : SAsm.Stmt := sequence [
  block [.ADDI .x7 .x0 23],
  .ite (.eq .x10 .x7) (block [.ADDI .x7 .x0 13])
    (sequence [block [.ADDI .x7 .x0 24], reject (.ne .x10 .x7) 6,
      block [.ADDI .x7 .x0 15]]),
  reject (.ne .x12 .x7) 1, range .x11 .x12,
  block [.ADDI .x7 .x0 23],
  .ite (.eq .x10 .x7) (readFields 2) (readFields 4), validFields, seconds]

private def yearSearch : SAsm.Stmt := sequence [
  block ([.ADDI .x15 .x0 1] ++ load .x16 10000 ++ [.ADDI .x5 .x15 1]),
  .loop (.ltu .x5 .x16) (sequence [
    block [.ADD .x17 .x15 .x16, .SRLI .x17 .x17 1],
    beforeYear .x17 .x28 .x30,
    .ite (.geu .x13 .x28) (block [.ADDI .x15 .x17 0]) (block [.ADDI .x16 .x17 0]),
    block [.ADDI .x5 .x15 1]]),
  beforeYear .x15 .x28 .x30, block [.SUB .x13 .x13 .x28]]

private def monthSearch : SAsm.Stmt := sequence [
  leap .x15 .x29,
  block [.ADDI .x30 .x0 1, .ADDI .x31 .x0 13, .ADDI .x5 .x30 1],
  .loop (.ltu .x5 .x31) (sequence [
    block [.ADD .x17 .x30 .x31, .SRLI .x17 .x17 1],
    beforeMonth .x17 .x29 .x28,
    .ite (.geu .x13 .x28) (block [.ADDI .x30 .x17 0]) (block [.ADDI .x31 .x17 0]),
    block [.ADDI .x5 .x30 1]]),
  beforeMonth .x30 .x29 .x28,
  block [.SUB .x13 .x13 .x28, .ADDI .x13 .x13 1]]

private def calendar : SAsm.Stmt := sequence [
  block (load .x7 (2^64-62135596800) ++ [.SLT .x5 .x10 .x7]),
  reject (.ne .x5 .x0) 6,
  block (load .x7 253402300799 ++ [.SLT .x5 .x7 .x10]),
  reject (.ne .x5 .x0) 6,
  block (load .x7 62135596800 ++ [.ADD .x10 .x10 .x7] ++ load .x7 86400 ++
    [.DIVU .x13 .x10 .x7, .REMU .x14 .x10 .x7]),
  yearSearch, monthSearch,
  block (load .x7 3600 ++ [.DIVU .x28 .x14 .x7, .ADDI .x7 .x0 60,
    .DIVU .x29 .x14 .x7, .REMU .x29 .x29 .x7, .REMU .x14 .x14 .x7])]

private def emitDigits (value : Reg) (offset width : Nat) : SAsm.Stmt := block <|
  (List.range width).flatMap fun i => [
    .ADDI .x7 .x0 (imm (10^(width-1-i))), .DIVU .x5 value .x7,
    .ADDI .x7 .x0 10, .REMU .x5 .x5 .x7, .ADDI .x5 .x5 48,
    .SB .x11 .x5 (imm (offset+i))]

private def emitFields (width : Nat) : SAsm.Stmt := sequence [
  emitDigits .x15 2 width, emitDigits .x30 (width+2) 2,
  emitDigits .x13 (width+4) 2, emitDigits .x28 (width+6) 2,
  emitDigits .x29 (width+8) 2, emitDigits .x14 (width+10) 2,
  block [.ADDI .x5 .x0 90, .SB .x11 .x5 (imm (width+12))]]

/-- a0=signed Unix seconds,a1=output,a2=capacity.
Writes a complete canonical DER time TLV (15/17 bytes), returns a0=status,a1=written.
Years1..9999 only. No stack or memory reads; errors never write output.
All callee-saved/ra/sp/gp/tp preserved; other caller-saved registers are zero. -/
def encode : SAsm.Stmt := sequence [calendar,
  block [.ADDI .x16 .x0 17, .ADDI .x17 .x0 24, .ADDI .x7 .x0 1950],
  .ite (.geu .x15 .x7) (sequence [block [.ADDI .x7 .x0 2047, .ADDI .x7 .x7 3],
    .ite (.ltu .x15 .x7) (block [.ADDI .x16 .x0 15, .ADDI .x17 .x0 23]) empty]) empty,
  reject (.ltu .x12 .x16) 5, range .x11 .x16,
  block [.SB .x11 .x17 0, .ADDI .x5 .x16 (-2), .SB .x11 .x5 1,
    .ADDI .x7 .x0 15],
  .ite (.eq .x16 .x7) (emitFields 2) (emitFields 4),
  block [.ADDI .x11 .x16 0], success]

/-- a0=NotBefore seconds,a1=NotAfter seconds,a2=UTC nanoseconds, all signed64.
Exact inclusive comparison uses signed128 products, not overflowing timestamps
or rounded seconds. Return0=valid,6=inverted interval,7=not yet,8=expired.
No memory or stack; all caller temps/results other than status are zero.
This numeric check does not establish clock trust or certificate authentication. -/
def validity : SAsm.Stmt := sequence [
  block [.SLT .x5 .x11 .x10], reject (.ne .x5 .x0) 6,
  block (load .x7 1000000000 ++ [
    .MUL .x13 .x10 .x7, .MULHU .x14 .x10 .x7,
    .SLT .x5 .x10 .x0, .MUL .x5 .x5 .x7, .SUB .x14 .x14 .x5,
    .SLT .x17 .x12 .x0, .SUB .x17 .x0 .x17,
    .SLT .x5 .x17 .x14]),
  reject (.ne .x5 .x0) 7,
  .ite (.eq .x17 .x14) (reject (.ltu .x12 .x13) 7) empty,
  block [.MUL .x15 .x11 .x7, .MULHU .x16 .x11 .x7,
    .SLT .x5 .x11 .x0, .MUL .x5 .x5 .x7, .SUB .x16 .x16 .x5,
    .SLT .x5 .x16 .x17],
  reject (.ne .x5 .x0) 8,
  .ite (.eq .x16 .x17) (reject (.ltu .x15 .x12) 8) empty, finish 0]

end Libp2pAsm.Asm.Identity.Time
