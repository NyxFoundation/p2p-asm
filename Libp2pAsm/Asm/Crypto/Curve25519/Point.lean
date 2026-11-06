import Libp2pAsm.Asm.Crypto.Curve25519.Common

namespace Libp2pAsm.Asm.Crypto.Curve25519.Point
open Rv64 Util Link

def d : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555

def operation (id : Nat) (out : Reg) (dst : Nat) (a : Reg) (ao : Nat)
    (b : Reg) (bo : Nat) : Part := .seq [
  .asm (block (ptr .x10 out dst ++ ptr .x11 a ao ++ ptr .x12 b bo)), .call id]

private def f (id dst a b : Nat) : Part := fieldCall id .x19 dst a b

/-- a0=out160,a1=P160,a2=Q160,a3=360-byte scratch. Complete extended Edwards
addition, matching RFC 8032 section 6 and HACL* point addition. Supports out=P/Q. -/
def add : Part := .seq [.asm enter,
  .asm (block [.ADDI .x8 .x10 0, .ADDI .x9 .x11 0,
    .ADDI .x18 .x12 0, .ADDI .x19 .x13 0]),
  operation 1 .x19 0 .x9 40 .x9 0, operation 1 .x19 320 .x18 40 .x18 0,
  f 2 0 0 320,
  operation 0 .x19 40 .x9 40 .x9 0, operation 0 .x19 320 .x18 40 .x18 0,
  f 2 40 40 320,
  operation 2 .x19 80 .x9 120 .x18 120,
  .asm (fieldConst .x19 320 ((2*d)%(2^255-19))), f 2 80 80 320,
  operation 2 .x19 120 .x9 80 .x18 80, f 0 120 120 120,
  f 1 160 40 0, f 1 200 120 80, f 0 240 120 80, f 0 280 40 0,
  operation 2 .x8 0 .x19 160 .x19 200, operation 2 .x8 40 .x19 240 .x19 280,
  operation 2 .x8 80 .x19 200 .x19 240, operation 2 .x8 120 .x19 160 .x19 280,
  .asm (block [.ADDI .x10 .x0 0]), .asm leave]

def identity (base : Reg) (offset : Nat) : SAsm.Stmt := sequence [
  fieldConst base offset 0, fieldConst base (offset+40) 1,
  fieldConst base (offset+80) 1, fieldConst base (offset+120) 0]

def basePoint (base : Reg) (offset : Nat) : SAsm.Stmt :=
  let x := 15112221349535400772501151409588531511454012693041857206046113283949847762202
  let y := 46316835694926478169428394003475163141307993866256225615783033603165251855960
  sequence [fieldConst base offset x, fieldConst base (offset+40) y,
    fieldConst base (offset+80) 1, fieldConst base (offset+120) (x*y%(2^255-19))]

private def scalarStep : Part := .seq [
  .asm (block [.ADDI .x10 .x19 0, .ADDI .x11 .x19 0, .ADDI .x12 .x19 0,
    .ADDI .x13 .x19 320]), .call 7,
  .asm (block [.ADDI .x10 .x19 160, .ADDI .x11 .x19 0, .ADDI .x12 .x9 0,
    .ADDI .x13 .x19 320]), .call 7,
  .asm (block [.ADDI .x20 .x20 (-1), .SRLI .x5 .x20 3, .ADD .x5 .x18 .x5,
    .LBU .x21 .x5 0, .ANDI .x6 .x20 7, .SRL .x21 .x21 .x6, .ANDI .x21 .x21 1]),
  .seq ((List.range 4).map fun i => .seq [
    .asm (block [.ADDI .x10 .x19 (imm (40*i)), .ADDI .x11 .x19 (imm (160+40*i)),
      .ADDI .x12 .x21 0]), .call 5])]

/-- a0=out160,a1=P160,a2=scalar32,a3=680-byte scratch. Fixed 256 iterations,
complete addition for both candidates and masked selection; no secret lookup. -/
def scalarMul : Part := .seq [.asm enter,
  .asm (block [.ADDI .x8 .x10 0, .ADDI .x9 .x11 0,
    .ADDI .x18 .x12 0, .ADDI .x19 .x13 0, .ADDI .x20 .x0 256]),
  .asm (identity .x19 0), .loop (.ne .x20 .x0) scalarStep,
  .asm (block [.ADDI .x11 .x0 160]), .asm (copy .x8 .x19 .x11),
  .asm (block [.ADDI .x10 .x0 0]), .asm leave]

/-- a0=encoded32,a1=P160,a2=232-byte scratch: inverse,x,y,power80,exponent32. -/
def encode : Part := .seq [.asm enter,
  .asm (block [.ADDI .x8 .x10 0, .ADDI .x9 .x11 0, .ADDI .x19 .x12 0]),
  .asm (bytesConst .x19 200 (2^255-21) 32),
  .asm (block [.ADDI .x10 .x19 0, .ADDI .x11 .x9 80,
    .ADDI .x12 .x19 200, .ADDI .x13 .x19 120]), .call 6,
  operation 2 .x19 40 .x9 0 .x19 0, operation 2 .x19 80 .x9 40 .x19 0,
  .asm (block [.ADDI .x10 .x8 0, .ADDI .x11 .x19 80]), .call 4,
  .asm (block [.LD .x5 .x19 40, .ANDI .x5 .x5 1, .SLLI .x5 .x5 7,
    .LBU .x6 .x8 31, .OR .x6 .x6 .x5, .SB .x8 .x6 31, .ADDI .x10 .x0 0]), .asm leave]

def callees : List Part := arithmeticCallees ++ [add,scalarMul,encode]

end Libp2pAsm.Asm.Crypto.Curve25519.Point
