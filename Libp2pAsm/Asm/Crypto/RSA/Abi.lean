import Libp2pAsm.Asm.Crypto.RSA.Limbs

namespace Libp2pAsm.Asm.Crypto.RSA
open Rv64 Util Link

def descriptorBytes : Nat := 128
def stackBytes : Nat := 288
def arithmeticByteLimit : Nat := 65536
def limbs (modulusBytes : Nat) : Nat := (modulusBytes+3)/4
def workspaceBytes (modulusBytes : Nat) : Nat := 56*limbs modulusBytes+896

/-- Conservative instruction estimator, not a proved whole-program bound.
Bounds all exponent bits, precomputation, SHA, copies and cleanup. -/
def workBound (modulusBytes exponentBytes : Nat) : Nat :=
  let l := limbs modulusBytes
  64*(l+1)^2*(16*exponentBytes+4) + 4096*l*l +
    50000*((modulusBytes+31)/32+2) + 1000*modulusBytes + 100000

def descriptorCheck : SAsm.Stmt := sequence [
  block [.ANDI .x5 .x10 7], reject (.ne .x5 .x0) 4,
  block [.ADDI .x7 .x0 128], range .x10 .x7,
  block [.ANDI .x5 .x2 15], reject (.ne .x5 .x0) 4,
  block [.ADDI .x7 .x0 288], reject (.ltu .x2 .x7) 4,
  block [.LD .x11 .x10 120], reject (.ltu .x11 .x7) 5]

def sizeCheck : SAsm.Stmt := sequence [
  block [.LD .x11 .x10 8, .LD .x12 .x10 24],
  reject (.eq .x11 .x0) 1, reject (.eq .x12 .x0) 1,
  reject (.ltu .x11 .x12) 1,
  block (load .x7 arithmeticByteLimit),
  reject (.ltu .x7 .x11) 5, reject (.ltu .x7 .x12) 5,
  block [.LD .x13 .x10 88, .LD .x14 .x10 96],
  reject (.ltu .x13 .x11) 5, reject (.ltu .x14 .x12) 5,
  block [.LD .x13 .x10 40], reject (.ne .x13 .x11) 2,
  block [.LD .x13 .x10 56, .ADDI .x7 .x0 32], reject (.ne .x13 .x7) 3,
  block (load .x7 2048), block [.LD .x13 .x10 104], reject (.ltu .x13 .x7) 5]

/-- a6=L, a7=exact scratch requirement; no multiplication can wrap after sizeCheck. -/
def resourceCheck : SAsm.Stmt := sequence [
  block [.ADDI .x16 .x11 3, .SRLI .x16 .x16 2,
    .ADDI .x7 .x0 56, .MUL .x17 .x16 .x7, .ADDI .x17 .x17 896,
    .LD .x13 .x10 72], reject (.ltu .x13 .x17) 5,
  block [.ADDI .x15 .x16 1, .MUL .x15 .x15 .x15, .SLLI .x15 .x15 6,
    .SLLI .x13 .x12 4, .ADDI .x13 .x13 4, .MUL .x15 .x15 .x13,
    .MUL .x13 .x16 .x16, .SLLI .x13 .x13 12, .ADD .x15 .x15 .x13,
    .ADDI .x13 .x11 31, .SRLI .x13 .x13 5, .ADDI .x13 .x13 2],
  block (load .x7 50000), block [.MUL .x13 .x13 .x7, .ADD .x15 .x15 .x13,
    .ADDI .x7 .x0 1000, .MUL .x13 .x11 .x7, .ADD .x15 .x15 .x13],
  block (load .x7 100000), block [.ADD .x15 .x15 .x7, .LD .x13 .x10 112],
  reject (.ltu .x13 .x15) 5]

def inputRange (offset : Nat) : SAsm.Stmt := sequence [
  block [.LD .x11 .x10 (imm offset), .LD .x12 .x10 (imm (offset+8))],
  range .x11 .x12]

/-- a1/a2 and a3/a4 are nonempty checked ranges. Subtraction avoids end overflow. -/
def disjointCheck : SAsm.Stmt := .ite (.ltu .x11 .x13)
  (sequence [block [.SUB .x7 .x13 .x11], reject (.ltu .x7 .x12) 4])
  (sequence [block [.SUB .x7 .x11 .x13], reject (.ltu .x7 .x14) 4])

def disjointInputs : SAsm.Stmt := sequence <|
  [block [.ADDI .x11 .x10 0, .ADDI .x12 .x0 128], disjointCheck] ++
  ([0,16,32,48].map fun offset => sequence [
    block [.LD .x11 .x10 (imm offset), .LD .x12 .x10 (imm (offset+8))], disjointCheck]) ++
  [block [.LD .x11 .x10 80, .ADDI .x12 .x0 512], disjointCheck]

def memoryCheck : SAsm.Stmt := sequence <|
  ([0,16,32,48].map inputRange) ++ [
  block [.LD .x11 .x10 80, .ADDI .x12 .x0 512], range .x11 .x12,
  block [.LD .x13 .x10 64], range .x13 .x17,
  block [.OR .x5 .x11 .x13, .ANDI .x5 .x5 7], reject (.ne .x5 .x0) 4,
  block [.ADDI .x14 .x17 0], disjointInputs,
  block [.ADDI .x11 .x2 (-288), .ADDI .x12 .x0 288], disjointCheck,
  block [.ADDI .x13 .x2 (-288), .ADDI .x14 .x0 288], disjointInputs]

def preflight : SAsm.Stmt := sequence [descriptorCheck, sizeCheck, resourceCheck, memoryCheck]

/-- Root context: s0=work, s1=descriptor, s2=L, s3=8L,
s4=base, s5=accumulator, s6=R2, s7=product, s8=subtraction, s9=fixed. -/
def beginWork : SAsm.Stmt := sequence [enter,
  block [.ADDI .x9 .x10 0, .LD .x8 .x9 64, .ADDI .x18 .x16 0,
    .SLLI .x19 .x18 3, .ADD .x20 .x8 .x19, .ADD .x21 .x20 .x19,
    .ADD .x22 .x21 .x19, .ADD .x23 .x22 .x19,
    .ADD .x24 .x23 .x19, .ADD .x24 .x24 .x19, .ADD .x25 .x24 .x19],
  wipe .x8 .x17,
  block [.ADDI .x11 .x2 (-176), .ADDI .x12 .x0 176], wipe .x11 .x12]

/-- a0=status. Wipes exact scratch and all 288 reserved stack bytes on content returns. -/
def endWork : SAsm.Stmt := sequence [
  block [.ADDI .x11 .x0 56, .MUL .x12 .x18 .x11, .ADDI .x12 .x12 896],
  wipe .x8 .x12, block [.ADDI .x11 .x2 (-176), .ADDI .x12 .x0 176],
  wipe .x11 .x12, leave]

def failWork (condition : SAsm.Cond) (status : Nat) : SAsm.Stmt :=
  .ite condition (sequence [block [.ADDI .x10 .x0 (imm status)], endWork]) empty

end Libp2pAsm.Asm.Crypto.RSA
