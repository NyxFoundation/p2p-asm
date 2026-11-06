import Libp2pAsm.Asm.Crypto.AES.Circuit

namespace Libp2pAsm.Asm.Crypto.AES
open Rv64

/-- Scratch layout: 123 circuit words, 8 padding bytes, state, shifted state.
All core fragments leave x1,x2,x3,x4 and all saved registers untouched. -/
def stateOffset : Nat := 992
def shiftOffset : Nat := 1008
def coreBytes : Nat := 1024

def imm (n : Nat) : BitVec 12 := BitVec.ofNat 12 n

def clearRegs : List Reg :=
  [.x5,.x6,.x7,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x28,.x29,.x30,.x31]

/-- x11=data pointer, x12=circuit; n is a public, compile-time byte count ≤16.
Clobbers x5,x6,x7,x28,x29,x30. The input plane slots are initialized each time. -/
def transposeIn (n : Nat) : SAsm.Stmt := sequence [
  .block ((List.range 8).map (fun i => Instr.SD .x12 .x0 (imm (8*i))) ++
    [.ADDI .x28 .x11 0, .ADDI .x29 .x0 0, .ADDI .x30 .x0 (imm n)]),
  .loop (.ltu .x29 .x30) (.block <|
    [.LBU .x7 .x28 0] ++ (List.range 8).flatMap (fun i =>
      [.SRLI .x5 .x7 (BitVec.ofNat 6 i), .ANDI .x5 .x5 1,
       .SLL .x5 .x5 .x29, .LD .x6 .x12 (imm (8*i)),
       .OR .x5 .x5 .x6, .SD .x12 .x5 (imm (8*i))]) ++
    [.ADDI .x28 .x28 1, .ADDI .x29 .x29 1])]

def transposeOut (n : Nat) : SAsm.Stmt := sequence [
  .block [.ADDI .x28 .x11 0, .ADDI .x29 .x0 0, .ADDI .x30 .x0 (imm n)],
  .loop (.ltu .x29 .x30) (.block <|
    [.ADDI .x7 .x0 0] ++ Circuit.outputs.zipIdx.flatMap (fun (w, i) =>
      [.LD .x5 .x12 (imm (8*w)), .SRL .x5 .x5 .x29, .ANDI .x5 .x5 1,
       .SLLI .x5 .x5 (BitVec.ofNat 6 i), .OR .x7 .x7 .x5]) ++
    [.SB .x28 .x7 0, .ADDI .x28 .x28 1, .ADDI .x29 .x29 1])]

def subBytes (n : Nat) : SAsm.Stmt := sequence [transposeIn n, Circuit.code, transposeOut n]

/-- x11=state, x15=current round key; advances x15 by 16. -/
def addRoundKey : SAsm.Stmt := sequence [
  .block [.ADDI .x28 .x11 0, .ADDI .x30 .x0 16],
  .loop (.ne .x30 .x0) (.block
    [.LBU .x5 .x28 0, .LBU .x6 .x15 0, .XOR .x5 .x5 .x6, .SB .x28 .x5 0,
     .ADDI .x28 .x28 1, .ADDI .x15 .x15 1, .ADDI .x30 .x30 (-1)])]

/-- ShiftRows writes the disjoint temporary state at x12+1008. -/
def shiftRows : SAsm.Stmt := .block <|
  (List.range 16).flatMap fun i =>
    [.LBU .x5 .x11 (imm (4*((i/4+i%4)%4)+i%4)), .SB .x12 .x5 (imm (shiftOffset+i))]

/-- Branchless polynomial reduction; input is an unsigned byte. -/
def xtime (dst src tmp : Reg) : List Instr :=
  [.SRLI tmp src 7, .SUB tmp .x0 tmp, .ANDI tmp tmp 0x1b,
   .SLLI dst src 1, .ANDI dst dst 255, .XOR dst dst tmp]

private def mixRow (a b : Reg) (i : Nat) : List Instr :=
  [.XOR .x17 a b] ++ xtime .x17 .x17 .x13 ++
  [.XOR .x17 .x17 a, .XOR .x17 .x17 .x14, .SB .x29 .x17 (imm i)]

/-- MixColumns uses a XOR total XOR xtime(a XOR b), no lookup tables. -/
def mixColumns : SAsm.Stmt := sequence [
  .block [.ADDI .x28 .x12 (imm shiftOffset), .ADDI .x29 .x11 0, .ADDI .x30 .x0 4],
  .loop (.ne .x30 .x0) (.block <|
    [.LBU .x5 .x28 0, .LBU .x6 .x28 1, .LBU .x7 .x28 2, .LBU .x31 .x28 3,
     .XOR .x14 .x5 .x6, .XOR .x14 .x14 .x7, .XOR .x14 .x14 .x31] ++
    mixRow .x5 .x6 0 ++ mixRow .x6 .x7 1 ++ mixRow .x7 .x31 2 ++ mixRow .x31 .x5 3 ++
    [.ADDI .x28 .x28 4, .ADDI .x29 .x29 4, .ADDI .x30 .x30 (-1)])]

/-- Byte copy supports arbitrary input/output alignment. Clobbers x5,x28..x30. -/
def copy (dst src : Reg) (n : Nat) : SAsm.Stmt := sequence [
  .block [.ADDI .x28 src 0, .ADDI .x29 dst 0, .ADDI .x30 .x0 (imm n)],
  .loop (.ne .x30 .x0) (.block
    [.LBU .x5 .x28 0, .SB .x29 .x5 0,
     .ADDI .x28 .x28 1, .ADDI .x29 .x29 1, .ADDI .x30 .x30 (-1)])]

/-- Core encryption: x10=176-byte expanded key, x11=16-byte state,
x12=1024-byte aligned workspace. These ranges are disjoint except the state
may be x12+992. All other caller-saved registers are clobbered. No return. -/
def encryptCore : SAsm.Stmt := sequence [
  .block [.ADDI .x15 .x10 0, .ADDI .x16 .x0 10], addRoundKey,
  .loop (.ne .x16 .x0) (sequence [subBytes 16, shiftRows,
    .block [.ADDI .x13 .x0 1],
    .ite (.eq .x16 .x13)
      (sequence [.block [.ADDI .x13 .x12 (imm shiftOffset)], copy .x11 .x13 16])
      mixColumns,
    addRoundKey, .block [.ADDI .x16 .x16 (-1)]])]

/-- x10=raw 16-byte key, x12=workspace, x15=176-byte expanded output.
The schedule uses 10 public rounds, four S-box bytes per round. -/
def expandCore : SAsm.Stmt := sequence [
  copy .x15 .x10 16,
  .block [.ADDI .x11 .x12 (imm stateOffset), .ADDI .x16 .x0 1, .ADDI .x15 .x15 16],
  .loop (.ne .x16 .x0) (sequence [
    .block ((List.range 4).flatMap fun i =>
      [.LBU .x5 .x15 (BitVec.ofInt 12 (Int.ofNat ((i+1)%4) - 4)), .SB .x11 .x5 (imm i)]),
    subBytes 4,
    .block ([.LBU .x5 .x11 0, .XOR .x5 .x5 .x16, .SB .x11 .x5 0] ++
      (List.range 16).flatMap (fun i =>
        [.LBU .x5 .x15 (BitVec.ofInt 12 (Int.ofNat i - 16))] ++
        (if i < 4 then [.LBU .x6 .x11 (imm i)]
         else [.LBU .x6 .x15 (imm (i-4))]) ++
        [.XOR .x5 .x5 .x6, .SB .x15 .x5 (imm i)]) ++
      xtime .x16 .x16 .x5 ++ [.ADDI .x15 .x15 16, .ADDI .x5 .x0 0x6c]),
    .ite (.eq .x16 .x5) (.block [.ADDI .x16 .x0 0]) (.block [])])]

/-- Wipe exactly n bytes, with public fixed bounds. -/
def wipe (base : Reg) (n : Nat) : SAsm.Stmt := sequence [
  .block [.ADDI .x28 base 0, .ADDI .x29 .x0 (imm n)],
  .loop (.ne .x29 .x0) (.block
    [.SB .x28 .x0 0, .ADDI .x28 .x28 1, .ADDI .x29 .x29 (-1)])]

end Libp2pAsm.Asm.Crypto.AES
