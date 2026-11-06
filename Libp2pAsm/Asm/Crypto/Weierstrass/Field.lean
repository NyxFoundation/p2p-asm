import Libp2pAsm.Asm.Crypto.Weierstrass.Limbs

namespace Libp2pAsm.Asm.Crypto.Weierstrass
open Rv64 Util Link
open Spec.Crypto.Weierstrass (Curve)

/-- Link indices: 0..2 field mul/add/sub, 3..5 scalar mul/add/sub,
6 field inverse, 7 scalar inverse, 8 complete point add, 9 scalar multiply,
10 projective-to-affine, 11 SHA256, 12 HMAC, 13 sqrt. -/
def invoke (target : Nat) (dst left right : Reg) (d l r : Nat) : Part := .seq [
  .asm (block [.ADDI .x10 dst (imm d), .ADDI .x11 left (imm l),
    .ADDI .x12 right (imm r)]), .call target]

def op (target d l r : Nat) : Part := invoke target .x8 .x8 .x8 d l r

/-- Fixed public exponent in Montgomery domain. a0=out32,a1=input32.
Frame: [0,32) accumulator,[32,64) base,[64,96) selected base,
[96,128) Montgomery one,[128,240) Util frame. Nested leaf adds 112 bytes.
Every exponent bit is a generation-time choice; zero input maps to zero for e>0. -/
def power (m exponent mulIndex : Nat) : Part := .seq <|
  [.asm enter, .asm (block [.ADDI .x2 .x2 (-128), .ADDI .x8 .x2 0,
    .ADDI .x9 .x10 0]), .asm (wordsCopy .x8 .x11 32 0),
    .asm (constant .x8 0 (2^256 % m))] ++
  ((List.range 256).flatMap fun i =>
    [op mulIndex 0 0 0] ++ (if exponent / 2^(255-i) % 2 == 1 then [op mulIndex 0 0 32] else [])) ++
  [.asm (wordsCopy .x9 .x8 0 0), .asm (zeroWords .x8 0 16),
    .asm (block [.ADDI .x2 .x2 128, .ADDI .x10 .x0 0]), .asm leave]

def fieldCallees (c : Curve) : List Part := [
  .asm (montMul c.prime), .asm (modAdd c.prime), .asm (modSub c.prime),
  .asm (montMul c.order), .asm (modAdd c.order), .asm (modSub c.order),
  power c.prime (c.prime-2) 0, power c.order (c.order-2) 3]

/-- Branchless full 256-bit zero check. result=0 or 1; clobbers t0/t1. -/
def isZero (src : Reg) (offset : Nat) (result : Reg) : SAsm.Stmt := block <|
  [.ADDI .x5 .x0 0] ++ (List.range 4).flatMap (fun i =>
    [.LD .x6 src (imm (offset+8*i)), .OR .x5 .x5 .x6]) ++
  [.SLTU result .x0 .x5, .XORI result result 1]

def equal (src : Reg) (l r : Nat) (result : Reg) : SAsm.Stmt := block <|
  [.ADDI .x7 .x0 0] ++ (List.range 4).flatMap (fun i =>
    [.LD .x5 src (imm (l+8*i)), .LD .x6 src (imm (r+8*i)),
      .XOR .x5 .x5 .x6, .OR .x7 .x7 .x5]) ++
  [.SLTU result .x0 .x7, .XORI result result 1]

end Libp2pAsm.Asm.Crypto.Weierstrass
