import Libp2pAsm.Asm.Crypto.Curve25519.Field

namespace Libp2pAsm.Asm.Crypto.Curve25519
open Rv64 Util Link

/-- Generation-time checked displacement construction, including offsets >2047. -/
def ptr (dst base : Reg) (offset : Nat) : List Instr :=
  if offset < 2048 then [.ADDI dst base (imm offset)]
  else load .x7 offset ++ [.ADD dst base .x7]

def fieldConst (base : Reg) (offset n : Nat) : SAsm.Stmt := block <|
  ptr .x30 base offset ++ ((List.range 5).flatMap fun i =>
    load .x5 (n / 2^(51*i) % 2^51) ++ [.SD .x30 .x5 (imm (8*i))])

def bytesConst (base : Reg) (offset n count : Nat) : SAsm.Stmt := block <|
  ptr .x30 base offset ++ ((List.range count).flatMap fun i =>
    [.ADDI .x5 .x0 (imm (n / 2^(8*i) % 256)), .SB .x30 .x5 (imm i)])

/-- Fixed offsets in one owned workspace. IDs 0 add, 1 sub, 2 mul, 3 decode,
4 encode, 5 swap, 6 power. All internal routines preserve s0..s11. -/
def fieldCall (id : Nat) (base : Reg) (dst a b : Nat) : Part := .seq [
  .asm (block (ptr .x10 base dst ++ ptr .x11 base a ++ ptr .x12 base b)), .call id]

def fieldCallees : List Part := [.asm Field.add, .asm Field.sub, .asm Field.mul,
  .asm Field.decode, .asm Field.encode, .asm Field.swap]

/-- a0=out, a1=base, a2=32-byte exponent, a3=80-byte scratch. Both multiply
and square run on every bit; select is a masked swap. 256 public iterations. -/
def powerBody : Part := .seq [
  .asm enter,
  .asm (block [.ADDI .x8 .x10 0, .ADDI .x9 .x11 0, .ADDI .x18 .x12 0,
    .ADDI .x19 .x13 0, .ADDI .x20 .x0 256]),
  .asm (fieldConst .x19 0 1),
  .loop (.ne .x20 .x0) (.seq [
    fieldCall 2 .x19 0 0 0,
    .asm (block [.ADDI .x10 .x19 40, .ADDI .x11 .x19 0, .ADDI .x12 .x9 0]), .call 2,
    .asm (block [.ADDI .x20 .x20 (-1), .SRLI .x5 .x20 3,
      .ADD .x5 .x18 .x5, .LBU .x12 .x5 0, .ANDI .x6 .x20 7,
      .SRL .x12 .x12 .x6, .ANDI .x12 .x12 1,
      .ADDI .x10 .x19 0, .ADDI .x11 .x19 40]), .call 5]),
  .asm (block [.ADDI .x11 .x0 40]), .asm (copy .x8 .x19 .x11),
  .asm (block [.ADDI .x10 .x0 0]), .asm leave]

def arithmeticCallees : List Part := fieldCallees ++ [powerBody]

/-- Half-open range overlap test via unsigned distance; permits zero-length
ranges and valid ranges ending at the top of address space. Clobbers t0/t1. -/
def disjoint (a n b m : Reg) : SAsm.Stmt :=
  .ite (.eq n .x0) empty (.ite (.eq m .x0) empty (sequence [
    .ite (.ltu a b)
      (sequence [block [.SUB .x5 b a], reject (.ltu .x5 n) 4])
      (sequence [block [.SUB .x5 a b], reject (.ltu .x5 m) 4])]))

/-- Stack arithmetic, alignment and owned-range checks precede any writes. -/
def stackCheck (depth : Nat) : SAsm.Stmt := sequence [
  block (load .x7 depth), reject (.ltu .x2 .x7) 4,
  block [.ANDI .x5 .x2 15], reject (.ne .x5 .x0) 4]

end Libp2pAsm.Asm.Crypto.Curve25519
