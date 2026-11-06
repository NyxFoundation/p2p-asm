import Libp2pAsm.Asm.Crypto.Link

/-! Radix 2^32 in zero-extended eight-byte slots. HACL* portable Montgomery
algorithm port; see Tests/RSA/README.md and LICENSES/hacl-rsa.txt.
All loop bounds and operands are public. These are private unchecked leaves. -/
namespace Libp2pAsm.Asm.Crypto.RSA
open Rv64 Util Link

/-- Decode exactly a2 BE bytes into zero-initialized slots at a0; source a1.
Clobbers only caller temps, leaves argument registers unchanged. -/
def decode : SAsm.Stmt := sequence [block [.ADDI .x5 .x0 0],
  .loop (.ltu .x5 .x12) (block [
    .SUB .x6 .x12 .x5, .ADDI .x6 .x6 (-1), .ADD .x6 .x11 .x6,
    .LBU .x7 .x6 0, .SRLI .x28 .x5 2, .SLLI .x28 .x28 3,
    .ADD .x28 .x10 .x28, .ANDI .x29 .x5 3, .SLLI .x29 .x29 3,
    .SLL .x7 .x7 .x29, .LD .x30 .x28 0, .OR .x30 .x30 .x7,
    .SD .x28 .x30 0, .ADDI .x5 .x5 1])]

/-- Encode a2 bytes from slots at a1 to BE at a0. -/
def encode : SAsm.Stmt := sequence [block [.ADDI .x5 .x0 0],
  .loop (.ltu .x5 .x12) (block [
    .SRLI .x6 .x5 2, .SLLI .x6 .x6 3, .ADD .x6 .x11 .x6,
    .LD .x7 .x6 0, .ANDI .x28 .x5 3, .SLLI .x28 .x28 3,
    .SRL .x7 .x7 .x28, .SUB .x29 .x12 .x5, .ADDI .x29 .x29 (-1),
    .ADD .x29 .x10 .x29, .SB .x29 .x7 0, .ADDI .x5 .x5 1])]

/-- s0=destination, s1=low candidate, s2=n, s3=L, s4=temporary,
s5=high carry. Subtract n, choose candidate iff high < borrow. -/
def normalize : SAsm.Stmt := sequence [
  block [.ADDI .x5 .x0 0, .ADDI .x6 .x0 0],
  .loop (.ltu .x5 .x19) (block [
    .SLLI .x7 .x5 3, .ADD .x28 .x9 .x7, .LD .x29 .x28 0,
    .ADD .x28 .x18 .x7, .LD .x30 .x28 0, .ADD .x30 .x30 .x6,
    .SLTU .x6 .x29 .x30, .SUB .x29 .x29 .x30,
    .SLLI .x29 .x29 32, .SRLI .x29 .x29 32,
    .ADD .x28 .x20 .x7, .SD .x28 .x29 0, .ADDI .x5 .x5 1]),
  .ite (.ltu .x21 .x6) (block [.ADDI .x20 .x9 0]) empty,
  block [.ADDI .x5 .x8 0, .ADDI .x6 .x20 0, .ADDI .x7 .x19 0],
  .loop (.ne .x7 .x0) (block [.LD .x28 .x6 0, .SD .x5 .x28 0,
    .ADDI .x5 .x5 8, .ADDI .x6 .x6 8, .ADDI .x7 .x7 (-1)])]

/-- a0=x, a1=n, a2=L, a3=temporary L slots. x<n; x := 2*x mod n.
Preserves s/ra/sp/gp/tp; 112-byte wiped frame. -/
def doubleMod : SAsm.Stmt := sequence [enter,
  block [.ADDI .x8 .x10 0, .ADDI .x9 .x10 0, .ADDI .x18 .x11 0,
    .ADDI .x19 .x12 0, .ADDI .x20 .x13 0, .ADDI .x21 .x0 0, .ADDI .x5 .x0 0],
  .loop (.ltu .x5 .x19) (block [
    .SLLI .x6 .x5 3, .ADD .x6 .x8 .x6, .LD .x7 .x6 0,
    .SLLI .x7 .x7 1, .ADD .x7 .x7 .x21, .SRLI .x21 .x7 32,
    .SLLI .x7 .x7 32, .SRLI .x7 .x7 32, .SD .x6 .x7 0, .ADDI .x5 .x5 1]),
  normalize, block [.ADDI .x10 .x0 0], leave]

/-- One inner product: t1=limb pointer, t2=product pointer, t3=multiplier,
t4=carry, t5=count. Every sum fits unsigned 64 bits. -/
def multiplyRow : SAsm.Stmt := .loop (.ne .x30 .x0) (block [
  .LD .x10 .x6 0, .LD .x11 .x7 0, .MUL .x10 .x10 .x28,
  .ADD .x10 .x10 .x11, .ADD .x10 .x10 .x29, .SRLI .x29 .x10 32,
  .SLLI .x10 .x10 32, .SRLI .x10 .x10 32, .SD .x7 .x10 0,
  .ADDI .x6 .x6 8, .ADDI .x7 .x7 8, .ADDI .x30 .x30 (-1)])

def product : SAsm.Stmt := sequence [
  block [.ADDI .x5 .x24 0, .SLLI .x6 .x19 1],
  .loop (.ne .x6 .x0) (block [.SD .x5 .x0 0, .ADDI .x5 .x5 8, .ADDI .x6 .x6 (-1)]),
  block [.ADDI .x5 .x0 0], .loop (.ltu .x5 .x19) (sequence [
    block [.SLLI .x7 .x5 3, .ADD .x6 .x22 .x7, .LD .x28 .x6 0,
      .ADD .x7 .x24 .x7, .ADDI .x6 .x23 0,
      .ADDI .x29 .x0 0, .ADDI .x30 .x19 0], multiplyRow,
    block [.SD .x7 .x29 0, .ADDI .x5 .x5 1]])]

/-- HACL* bn_mont_reduction_u32: the extra carry is threaded across rows. -/
def reduction : SAsm.Stmt := sequence [
  block [.ADDI .x5 .x0 0, .ADDI .x21 .x0 0],
  .loop (.ltu .x5 .x19) (sequence [
    block [.SLLI .x7 .x5 3, .ADD .x7 .x24 .x7, .LD .x28 .x7 0,
      .MUL .x28 .x28 .x25, .SLLI .x28 .x28 32, .SRLI .x28 .x28 32,
      .ADDI .x6 .x18 0, .ADDI .x29 .x0 0, .ADDI .x30 .x19 0],
    multiplyRow,
    block [.LD .x10 .x7 0, .ADD .x10 .x10 .x29, .ADD .x10 .x10 .x21,
      .SRLI .x21 .x10 32, .SLLI .x10 .x10 32, .SRLI .x10 .x10 32,
      .SD .x7 .x10 0, .ADDI .x5 .x5 1]]),
  block [.SLLI .x9 .x19 3, .ADD .x9 .x24 .x9], normalize]

/-- a0=out, a1=a, a2=b, a3=n, a4=L, a5=-n[0]^-1 mod 2^32,
a6=2L product slots, a7=L temporary slots. a,b<n and n odd >1.
out may equal a/b. All other ranges disjoint. Result a*b/R mod n.
112-byte wiped frame; caller owns/wipes product and temporary. -/
def montgomery : SAsm.Stmt := sequence [enter,
  block [.ADDI .x8 .x10 0, .ADDI .x22 .x11 0, .ADDI .x23 .x12 0,
    .ADDI .x18 .x13 0, .ADDI .x19 .x14 0, .ADDI .x25 .x15 0,
    .ADDI .x24 .x16 0, .ADDI .x20 .x17 0],
  product, reduction, block [.ADDI .x10 .x0 0], leave]

end Libp2pAsm.Asm.Crypto.RSA
