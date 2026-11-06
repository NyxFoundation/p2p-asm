import Libp2pAsm.Asm.Crypto.Link
import Libp2pAsm.Spec.Crypto.Weierstrass.Basic

/-! RV64 translations of HACL* bn_mul4, mont_reduction, bn_add_mod4,
bn_sub_mod4 and fiat-crypto carry/select idioms; generic odd 256-bit modulus.
Pinned source and actual MIT notices: Tests/Weierstrass/README.md, LICENSES/.
All buffers below are four aligned little-endian uint64 limbs. Private contracts
require canonical inputs. Every address/iteration is independent of their values.
No runtime call to the imported specification: its numbers are generation data. -/
namespace Libp2pAsm.Asm.Crypto.Weierstrass
open Rv64 Util Link
open Spec.Crypto.Weierstrass (Curve)

def limb (n i : Nat) : Nat := n / 2^(64*i) % 2^64

def constant (base : Reg) (offset value : Nat) : SAsm.Stmt := block <|
  (List.range 4).flatMap fun i => load .x5 (limb value i) ++ [.SD base .x5 (imm (offset+8*i))]

def wordsCopy (dst src : Reg) (d s : Nat) (count : Nat := 4) : SAsm.Stmt := block <|
  (List.range count).flatMap fun i => [.LD .x5 src (imm (s+8*i)), .SD dst .x5 (imm (d+8*i))]

def zeroWords (base : Reg) (offset count : Nat) : SAsm.Stmt := block <|
  (List.range count).map fun i => .SD base .x0 (imm (offset+8*i))

/-- x5+x6+carry(x13); result x7 and next carry x13. -/
def adc : List Instr := [.ADD .x7 .x5 .x6, .SLTU .x28 .x7 .x5,
  .ADD .x29 .x7 .x13, .SLTU .x30 .x29 .x7,
  .OR .x13 .x28 .x30, .ADDI .x7 .x29 0]

/-- x5-x6-borrow(x13); result x7 and next borrow x13. -/
def sbb : List Instr := [.SUB .x7 .x5 .x6, .SLTU .x28 .x5 .x6,
  .SLTU .x30 .x7 .x13, .SUB .x7 .x7 .x13, .OR .x13 .x28 .x30]

def maskSelect (dst left right : Reg) (mask : Reg) (count : Nat := 4) : SAsm.Stmt := block <|
  (List.range count).flatMap fun i => [.LD .x5 left (imm (8*i)), .LD .x6 right (imm (8*i)),
    .XOR .x7 .x5 .x6, .AND .x7 .x7 mask, .XOR .x7 .x7 .x6, .SD dst .x7 (imm (8*i))]

/-- Reduce a five-limb candidate at sp+32; high limb in a4 (0 or 1).
The candidate is <2m. Subtraction is always computed, then selected by mask. -/
def reduce (m : Nat) : SAsm.Stmt := sequence [block <|
  [.ADDI .x13 .x0 0] ++ (List.range 4).flatMap (fun i =>
    [.LD .x5 .x2 (imm (32+8*i))] ++ load .x6 (limb m i) ++ sbb ++
      [.SD .x2 .x7 (imm (64+8*i))]),
  block [.SUB .x14 .x14 .x13, .ADDI .x11 .x2 32, .ADDI .x12 .x2 64],
  maskSelect .x10 .x11 .x12 .x14]

/-- Low/high product plus two words fits in 128 bits. -/
def mulAdd (offset : Nat) : List Instr := [
  .MUL .x7 .x5 .x6, .MULHU .x28 .x5 .x6,
  .ADD .x7 .x7 .x13, .SLTU .x30 .x7 .x13, .ADD .x28 .x28 .x30,
  .LD .x29 .x2 (imm offset), .ADD .x7 .x7 .x29,
  .SLTU .x30 .x7 .x29, .ADD .x13 .x28 .x30, .SD .x2 .x7 (imm offset)]

def product : SAsm.Stmt := block <| (List.range 4).flatMap fun i =>
  [.LD .x6 .x12 (imm (8*i)), .ADDI .x13 .x0 0] ++
  (List.range 4).flatMap (fun j => [.LD .x5 .x11 (imm (8*j))] ++ mulAdd (8*(i+j))) ++
  [.SD .x2 .x13 (imm (8*(4+i)))]

/-- Newton's inverse, generation time only. Six doublings give 64 bits. -/
def negInverse (m : Nat) : Nat :=
  let x := (List.range 6).foldl (fun x _ => (x*(2+2^128-m%2^64*x)) % 2^64) 1
  (2^64-x) % 2^64

def montReduce (m : Nat) : SAsm.Stmt := sequence [block [.ADDI .x14 .x0 0],
  block <| (List.range 4).flatMap fun i =>
    [.LD .x15 .x2 (imm (8*i))] ++ load .x5 (negInverse m) ++
    [.MUL .x15 .x15 .x5, .ADDI .x13 .x0 0] ++
    (List.range 4).flatMap (fun j => load .x5 (limb m j) ++
      [.ADDI .x6 .x15 0] ++ mulAdd (8*(i+j))) ++
    [.LD .x5 .x2 (imm (8*(4+i))), .ADDI .x6 .x13 0, .ADDI .x13 .x14 0] ++
    adc ++ [.SD .x2 .x7 (imm (8*(4+i))), .ADDI .x14 .x13 0], reduce m]

def leafExit : SAsm.Stmt := sequence [zeroWords .x2 0 14,
  block [.ADDI .x2 .x2 112], finish]

/-- a0=out, a1=x, a2=y. All may alias. Owns/wipes 112 stack bytes.
Canonical x,y<m; output=x*y*2^-256 mod m. Preserves all s-regs/ra/sp/gp/tp. -/
def montMul (m : Nat) : SAsm.Stmt := sequence [block [.ADDI .x2 .x2 (-112)],
  zeroWords .x2 0 14, product, montReduce m, leafExit]

def modAdd (m : Nat) : SAsm.Stmt := sequence [block [.ADDI .x2 .x2 (-112)],
  block <| [.ADDI .x13 .x0 0] ++ (List.range 4).flatMap (fun i =>
    [.LD .x5 .x11 (imm (8*i)), .LD .x6 .x12 (imm (8*i))] ++ adc ++
      [.SD .x2 .x7 (imm (32+8*i))]),
  block [.ADDI .x14 .x13 0], reduce m, leafExit]

def modSub (m : Nat) : SAsm.Stmt := sequence [block [.ADDI .x2 .x2 (-112)],
  block <| [.ADDI .x13 .x0 0] ++ (List.range 4).flatMap (fun i =>
    [.LD .x5 .x11 (imm (8*i)), .LD .x6 .x12 (imm (8*i))] ++ sbb ++
      [.SD .x2 .x7 (imm (32+8*i))]),
  block <| [.SUB .x14 .x0 .x13, .ADDI .x13 .x0 0] ++
    (List.range 4).flatMap (fun i => [.LD .x5 .x2 (imm (32+8*i))] ++
      load .x6 (limb m i) ++ [.AND .x6 .x6 .x14] ++ adc ++ [.SD .x10 .x7 (imm (8*i))]),
  leafExit]

/-- Byte conversion accepts any external alignment; internal limbs are aligned. -/
def decode (dst src : Reg) (d s : Nat) : SAsm.Stmt := block <|
  (List.range 4).flatMap fun i => [.ADDI .x5 .x0 0] ++
    (List.range 8).flatMap (fun j => [.LBU .x6 src (imm (s+8*(3-i)+j)),
      .SLLI .x5 .x5 8, .OR .x5 .x5 .x6]) ++ [.SD dst .x5 (imm (d+8*i))]

def encode (dst src : Reg) (d s : Nat) : SAsm.Stmt := block <|
  (List.range 4).flatMap fun i => [.LD .x6 src (imm (s+8*i))] ++
    storeBE dst .x6 (d+8*(3-i)) 8

/-- Set result=1 iff input<m (and optionally nonzero). Constant trace. -/
def canonical (src : Reg) (offset m : Nat) (result : Reg) (nonzero := false) : SAsm.Stmt := block <|
  [.ADDI .x13 .x0 0, .ADDI .x15 .x0 0] ++
  (List.range 4).flatMap (fun i => [.LD .x5 src (imm (offset+8*i)), .OR .x15 .x15 .x5] ++
    load .x6 (limb m i) ++ sbb) ++
  (if nonzero then [.SLTU .x15 .x0 .x15, .AND .x13 .x13 .x15] else []) ++
  [.ADDI result .x13 0]

end Libp2pAsm.Asm.Crypto.Weierstrass
