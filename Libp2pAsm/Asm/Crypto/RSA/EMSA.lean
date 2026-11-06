import Libp2pAsm.Asm.Crypto.RSA.Public
import Libp2pAsm.Asm.Crypto.SHA256

namespace Libp2pAsm.Asm.Crypto.RSA
open Rv64 Util Link

/-- Exact RFC 8017 SHA256 DigestInfo, including NULL parameters. Literal bytes
are emitted as instructions, independent from the mathematical spec. -/
def pkcsPrefix : List Nat :=
  [0x30,0x31,0x30,0x0d,0x06,0x09,0x60,0x86,0x48,0x01,
   0x65,0x03,0x04,0x02,0x01,0x05,0x00,0x04,0x20]

def pkcs : SAsm.Stmt := sequence <| [
  block [.LD .x21 .x9 8, .LBU .x5 .x20 0], failWork (.ne .x5 .x0) 2,
  block [.LBU .x5 .x20 1, .ADDI .x7 .x0 1], failWork (.ne .x5 .x7) 2,
  block [.ADDI .x22 .x21 (-52), .ADDI .x23 .x0 2, .ADDI .x7 .x0 255],
  .loop (.ltu .x23 .x22) (sequence [
    block [.ADD .x6 .x20 .x23, .LBU .x5 .x6 0], failWork (.ne .x5 .x7) 2,
    block [.ADDI .x23 .x23 1]]),
  block [.ADD .x22 .x20 .x22, .LBU .x5 .x22 0], failWork (.ne .x5 .x0) 2] ++
  (pkcsPrefix.zipIdx.map fun (byte,i) => sequence [
    block [.LBU .x5 .x22 (imm (i+1)), .ADDI .x7 .x0 (imm byte)],
    failWork (.ne .x5 .x7) 2]) ++ [
  block [.ADDI .x22 .x22 20, .LD .x23 .x9 48, .ADDI .x24 .x0 32],
  .loop (.ne .x24 .x0) (sequence [
    block [.LBU .x5 .x22 0, .LBU .x6 .x23 0], failWork (.ne .x5 .x6) 2,
    block [.ADDI .x22 .x22 1, .ADDI .x23 .x23 1, .ADDI .x24 .x24 (-1)]])]

/-- Fixed SHA output at fixed+816, workspace fixed+0, table from descriptor.
Input is a0/a1. Whole.body uses actual typed SHA rounds, no host callback. -/
def sha : Part := .seq [.asm (block [
  .ADDI .x12 .x25 816, .ADDI .x13 .x25 0, .ADDI .x14 .x0 704,
  .LD .x15 .x9 80]), .call 2]

/-- s4=EM, s5=dbLen, s6=H, s7=MGF counter, s8=DB offset,
s10=top-byte allowed mask. Handles emLen=k-1 without truncating its leading byte. -/
def pssShape : SAsm.Stmt := sequence [
  block [.LD .x26 .x25 848, .ADDI .x26 .x26 (-1),
    .ADDI .x21 .x26 7, .SRLI .x21 .x21 3, .LD .x5 .x9 8],
  .ite (.ne .x21 .x5) (sequence [block [.LBU .x6 .x20 0],
    failWork (.ne .x6 .x0) 2, block [.ADDI .x20 .x20 1]]) empty,
  block [.SLLI .x5 .x21 3, .SUB .x5 .x5 .x26,
    .ADDI .x26 .x0 255, .SRL .x26 .x26 .x5,
    .LBU .x6 .x20 0, .XORI .x7 .x26 255, .AND .x6 .x6 .x7],
  failWork (.ne .x6 .x0) 2,
  block [.ADD .x5 .x20 .x21, .LBU .x6 .x5 (-1), .ADDI .x7 .x0 188],
  failWork (.ne .x6 .x7) 2,
  block [.ADDI .x21 .x21 (-33), .ADD .x22 .x20 .x21,
    .ADDI .x11 .x25 776, .ADDI .x12 .x0 32], copy .x11 .x22 .x12,
  block [.ADDI .x23 .x0 0, .ADDI .x24 .x0 0]]

def mgf : Part := .loop (.ltu .x24 .x21) (.seq [
  .asm (block (storeBE .x25 .x23 808 4)),
  .asm (block [.ADDI .x10 .x25 776, .ADDI .x11 .x0 36]), sha,
  .asm (block [.ADDI .x5 .x0 0, .ADDI .x7 .x0 32,
    .SUB .x6 .x21 .x24]),
  .asm (.ite (.ltu .x6 .x7) (block [.ADDI .x7 .x6 0]) empty),
  .asm (.loop (.ltu .x5 .x7) (block [
    .ADD .x6 .x20 .x24, .ADD .x6 .x6 .x5, .LBU .x28 .x6 0,
    .ADD .x29 .x25 .x5, .LBU .x30 .x29 816,
    .XOR .x28 .x28 .x30, .SB .x6 .x28 0, .ADDI .x5 .x5 1])),
  .asm (block [.ADD .x24 .x24 .x7, .ADDI .x23 .x23 1])])

def pssDB : SAsm.Stmt := sequence [
  block [.LBU .x5 .x20 0, .AND .x5 .x5 .x26, .SB .x20 .x5 0,
    .ADDI .x23 .x21 (-33), .ADDI .x24 .x0 0],
  .loop (.ltu .x24 .x23) (sequence [
    block [.ADD .x6 .x20 .x24, .LBU .x5 .x6 0], failWork (.ne .x5 .x0) 2,
    block [.ADDI .x24 .x24 1]]),
  block [.ADD .x23 .x20 .x23, .LBU .x5 .x23 0, .ADDI .x7 .x0 1],
  failWork (.ne .x5 .x7) 2,
  block [.SD .x25 .x0 704, .ADDI .x11 .x25 712,
    .LD .x12 .x9 48, .ADDI .x13 .x0 32], copy .x11 .x12 .x13,
  block [.ADDI .x11 .x25 744, .ADDI .x12 .x23 1], copy .x11 .x12 .x13]

def pss : Part := .seq [.asm pssShape, mgf, .asm pssDB,
  .asm (block [.ADDI .x10 .x25 704, .ADDI .x11 .x0 72]), sha,
  .asm (block [.ADDI .x23 .x25 816, .ADDI .x24 .x0 32]),
  .asm (.loop (.ne .x24 .x0) (sequence [
    block [.LBU .x5 .x22 0, .LBU .x6 .x23 0], failWork (.ne .x5 .x6) 2,
    block [.ADDI .x22 .x22 1, .ADDI .x23 .x23 1, .ADDI .x24 .x24 (-1)]]))]

end Libp2pAsm.Asm.Crypto.RSA
