import Libp2pAsm.Asm.Crypto.Curve25519.Common

namespace Libp2pAsm.Asm.Crypto.Curve25519.Scalar
open Rv64 Util Link

def order : Nat := 2^252 + 27742317777372353535851937790883648493
def limbs : List Reg := [.x13,.x14,.x15,.x16]

/-- Four-word subtraction with two explicit borrow tests per word. Input <2*l;
output canonical. The final borrow drives a mask, never a conditional branch. -/
def reduceOnce : List Instr :=
  let differences : List Reg := [.x5,.x6,.x7,.x28]
  [.ADDI .x30 .x0 0] ++ ((limbs.zip differences).zipIdx.flatMap fun ((a,b),i) =>
    load .x29 (order / 2^(64*i) % 2^64) ++
    [.SUB b a .x29, .SLTU .x31 a .x29, .SLTU .x17 b .x30,
     .SUB b b .x30, .OR .x30 .x31 .x17]) ++
  [.ADDI .x30 .x30 (-1)] ++ ((limbs.zip differences).flatMap fun (a,b) =>
    [.XOR b a b, .AND b b .x30, .XOR a a b])

private def double : List Instr := [.ADDI .x10 .x0 0] ++
  (limbs.flatMap fun r => [.SRLI .x11 r 63, .SLLI r r 1,
    .OR r r .x10, .ADDI .x10 .x11 0])

private def store : List Instr := (limbs.zipIdx.flatMap fun (r,i) =>
  (List.range 8).flatMap fun j =>
    [.SRLI .x5 r (BitVec.ofNat 6 (8*j)), .SB .x8 .x5 (imm (8*i+j))])

/-- a0=32-byte destination, a1=input bytes, a2=public byte count (32 or 64).
Binary long reduction; 8*count iterations; works for arbitrary 512-bit inputs. -/
def reduce : Part := .seq [.asm enter,
  .asm (block ([.ADDI .x8 .x10 0, .ADDI .x9 .x11 0, .SLLI .x18 .x12 3] ++
    limbs.map (fun r => .ADDI r .x0 0))),
  .loop (.ne .x18 .x0) (.asm (block <| double ++
    [.ADDI .x18 .x18 (-1), .SRLI .x10 .x18 3, .ADD .x10 .x9 .x10,
     .LBU .x10 .x10 0, .ANDI .x11 .x18 7, .SRL .x10 .x10 .x11,
     .ANDI .x10 .x10 1, .OR .x13 .x13 .x10] ++ reduceOnce)),
  .asm (block (store ++ [.ADDI .x10 .x0 0])), .asm leave]

/-- Add masked canonical operand at s2. Mask in s5; no secret addresses. -/
private def addMasked : List Instr := [.ADDI .x12 .x0 0] ++
  (limbs.zipIdx.flatMap fun (r,i) =>
    [.LD .x10 .x18 (imm (8*i)), .AND .x10 .x10 .x21,
     .ADD r r .x10, .SLTU .x11 r .x10, .ADD r r .x12,
     .SLTU .x17 r .x12, .OR .x12 .x11 .x17]) ++ reduceOnce

/-- a0=out32,a1=k32,a2=a32,a3=r32, all scalars canonical and 8-aligned except
output; compute (k*a+r) mod l. Constant 256-step double-and-add multiplication. -/
def mulAdd : Part := .seq [.asm enter,
  .asm (block ([.ADDI .x8 .x10 0, .ADDI .x9 .x11 0, .ADDI .x18 .x12 0,
    .ADDI .x19 .x13 0, .ADDI .x20 .x0 256] ++ limbs.map (fun r => .ADDI r .x0 0))),
  .loop (.ne .x20 .x0) (.asm (block <| double ++ reduceOnce ++
    [.ADDI .x20 .x20 (-1), .SRLI .x10 .x20 3, .ADD .x10 .x9 .x10,
     .LBU .x10 .x10 0, .ANDI .x11 .x20 7, .SRL .x10 .x10 .x11,
     .ANDI .x10 .x10 1, .SUB .x21 .x0 .x10] ++ addMasked)),
  .asm (block ([.ADDI .x18 .x19 0, .ADDI .x21 .x0 (-1)] ++ addMasked ++
    store ++ [.ADDI .x10 .x0 0])), .asm leave]

end Libp2pAsm.Asm.Crypto.Curve25519.Scalar
