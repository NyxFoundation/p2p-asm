import Libp2pAsm.Asm.Crypto.AES.Core

namespace Libp2pAsm.Asm.Crypto.AES
open Rv64

/-- 0=success; 1=key length; 2=block length; 3=output capacity;
4=workspace capacity. Pointer validity/disjointness are caller obligations. -/
def finish (status : Nat) : SAsm.Stmt := sequence [
  .block ((clearRegs.map fun r => Instr.ADDI r .x0 0) ++ [.ADDI .x10 .x0 (imm status)]), .ret]

def reject (c : SAsm.Cond) (status : Nat) : SAsm.Stmt :=
  .ite c (finish status) (.block [])

/-- Leaf key expansion ABI: a0=key, a1=key length (16), a2=output,
a3=output capacity (≥176), a4=8-aligned scratch, a5=scratch capacity (≥1024).
Raw key, output, workspace and code are disjoint nonwrapping valid ranges;
only output and workspace are writable. Output/key may be byte-unaligned.
Success writes exactly 176 output bytes and wipes 1024 scratch bytes.
Validation errors write no memory. No stack used. ra/sp/gp/tp/s0..s11 preserved;
all remaining caller-saved registers are cleared except a0=status. -/
def expand : SAsm.Stmt := sequence [
  .block [.ADDI .x5 .x0 16], reject (.ne .x11 .x5) 1,
  .block [.ADDI .x5 .x0 176], reject (.ltu .x13 .x5) 3,
  .block [.ADDI .x5 .x0 1024], reject (.ltu .x15 .x5) 4,
  .block [.ADDI .x15 .x12 0, .ADDI .x12 .x14 0],
  expandCore, wipe .x12 1024, finish 0]

/-- Leaf block/header-protection ABI: a0=176-byte expanded key,
a1=16-byte input, a2=input length, a3=output, a4=output capacity,
a5=8-aligned 1024-byte scratch, a6=scratch capacity. All payload ranges and
16 owned bytes below 16-aligned sp are disjoint, nonwrapping, valid and separate
from code. Input/key/output can be unaligned. Output is 16 bytes for AES,
5 for QUIC header protection. Error returns change no memory; success wipes
scratch and the owned stack frame. Preserves ra/sp/gp/tp and all saved registers.
Clears all other caller-saved registers except a0=status. -/
def encrypt (headerProtection : Bool := false) : SAsm.Stmt :=
  let count := if headerProtection then 5 else 16
  sequence [
    .block [.ADDI .x5 .x0 16], reject (.ne .x12 .x5) 2,
    .block [.ADDI .x5 .x0 (imm count)], reject (.ltu .x14 .x5) 3,
    .block [.ADDI .x5 .x0 1024], reject (.ltu .x16 .x5) 4,
    .block [.ADDI .x2 .x2 (-16), .SD .x2 .x13 0, .SD .x2 .x0 8,
      .ADDI .x12 .x15 0, .ADDI .x13 .x11 0, .ADDI .x11 .x12 (imm stateOffset)],
    copy .x11 .x13 16, encryptCore,
    .block [.LD .x13 .x2 0], copy .x13 .x11 count,
    wipe .x12 1024,
    .block [.SD .x2 .x0 0, .SD .x2 .x0 8, .ADDI .x2 .x2 16], finish 0]

def headerProtection : SAsm.Stmt := encrypt true

end Libp2pAsm.Asm.Crypto.AES
