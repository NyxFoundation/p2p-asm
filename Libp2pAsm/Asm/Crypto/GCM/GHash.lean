import Libp2pAsm.Asm.Crypto.AES.Api

namespace Libp2pAsm.Asm.Crypto.GCM
open Rv64
open AES (imm)

/-- Big-endian byte loads avoid any alignment precondition for wire buffers. -/
def loadBE (dst base tmp : Reg) (offset : Nat) : List Instr :=
  [.ADDI dst .x0 0] ++ (List.range 8).flatMap fun i =>
    [.LBU tmp base (imm (offset+i)), .SLLI dst dst 8, .OR dst dst tmp]

def storeBE (src base tmp : Reg) (offset : Nat) : List Instr :=
  (List.range 8).flatMap fun i =>
    [.SRLI tmp src (BitVec.ofNat 6 (8*(7-i))), .SB base tmp (imm (offset+i))]

/-- x5:x6 is X, x7:x28 is V, x29:x30 is Z (high:low).
Fixed 128 iterations; high-bit masks replace all data-dependent choices.
Clobbers x13..x17,x31. Polynomial e1||0^120 is a public immediate. -/
def multiply : SAsm.Stmt := sequence [
  .block [.ADDI .x29 .x0 0, .ADDI .x30 .x0 0, .ADDI .x31 .x0 128,
    .ADDI .x15 .x0 0xe1, .SLLI .x15 .x15 56],
  .loop (.ne .x31 .x0) (.block [
    .SRAI .x13 .x5 63, .AND .x14 .x7 .x13, .XOR .x29 .x29 .x14,
    .AND .x14 .x28 .x13, .XOR .x30 .x30 .x14,
    .ANDI .x13 .x28 1, .SUB .x13 .x0 .x13, .AND .x13 .x13 .x15,
    .SLLI .x14 .x7 63, .SRLI .x28 .x28 1, .OR .x28 .x28 .x14,
    .SRLI .x7 .x7 1, .XOR .x7 .x7 .x13,
    .SRLI .x14 .x6 63, .SLLI .x5 .x5 1, .OR .x5 .x5 .x14,
    .SLLI .x6 .x6 1, .ADDI .x31 .x31 (-1)])]

/-- Core GHASH update: a0=accumulator, a1=H, a2=block (all 16 bytes).
Accumulator is writable; H/block readable and disjoint. All can be unaligned.
Only actual loads, shifts, masks, xor and stores; no external cryptographic call.
The core retains a0,a1,a2; all other caller-saved registers may be clobbered. -/
def updateCore : SAsm.Stmt := sequence [
  .block (loadBE .x5 .x10 .x13 0 ++ loadBE .x6 .x10 .x13 8 ++
    loadBE .x7 .x12 .x13 0 ++ loadBE .x28 .x12 .x13 8 ++
    [.XOR .x5 .x5 .x7, .XOR .x6 .x6 .x28] ++
    loadBE .x7 .x11 .x13 0 ++ loadBE .x28 .x11 .x13 8),
  multiply,
  .block (storeBE .x29 .x10 .x13 0 ++ storeBE .x30 .x10 .x13 8)]

/-- Fixed-size leaf GHASH update ABI as updateCore. No stack or workspace;
preserves ra/sp/gp/tp and all saved registers. Clears caller-saved registers,
returns a0=0. Valid nonwrapping disjoint ranges are caller obligations. -/
def update : SAsm.Stmt := sequence [updateCore, AES.finish 0]

end Libp2pAsm.Asm.Crypto.GCM
