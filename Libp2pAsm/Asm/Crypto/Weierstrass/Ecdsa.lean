import Libp2pAsm.Asm.Crypto.Weierstrass.Signature

namespace Libp2pAsm.Asm.Crypto.Weierstrass
open Rv64 Util Link
open Spec.Crypto.Weierstrass (Curve)

def signatureStatus : Part := .seq [
  .asm (isZero .x8 64 .x22), .asm (block [.XORI .x22 .x22 1, .AND .x23 .x23 .x22]),
  .asm (isZero .x8 96 .x22), .asm (block [.XORI .x22 .x22 1, .AND .x23 .x23 .x22,
    .XORI .x23 .x23 1, .AND .x23 .x23 .x18, .ADDI .x5 .x0 10,
    .MUL .x23 .x23 .x5, .OR .x19 .x19 .x23])]

/-- Compact32+32 bytes, big endian. Secret d0,z32,r64,s96,k128,kinv160.
The only conditional selections involving secrets use masks, never branches. -/
def signArithmetic (c : Curve) : Part := .seq [
  basePoint c 192, op 9 288 128 192, op 10 288 288 288,
  .asm (zeroWords .x8 640 4), op 4 64 288 640,
  op 3 0 0 608, op 3 128 128 608, op 7 160 128 128,
  op 3 640 64 608, op 3 672 640 0, op 3 32 32 608,
  op 4 672 672 32, op 3 96 160 672, op 3 96 96 544,
  signatureStatus,
  if c == .secp256k1 then .seq [
    .asm (canonical .x8 96 (c.order/2+1) .x22),
    .asm (block [.ADDI .x25 .x22 (-1)]), .asm (zeroWords .x8 640 4), op 5 640 640 96,
    .asm (block [.ADDI .x10 .x8 96, .ADDI .x11 .x8 640, .ADDI .x12 .x8 96]),
    .asm (maskSelect .x10 .x11 .x12 .x25)] else .asm empty]

def sign (c : Curve) (compact : Bool := false) : Except String SAsm.Stmt :=
  let size := if compact then 64 else 80
  program (.seq [.asm descriptorCheck, .asm (inputCheck 0 32), .asm (inputCheck 32 32),
    .asm (buffersCheck size true), .asm beginWork, setupConstants c, secretScalar c,
    nonce c, signArithmetic c,
    (if compact then .asm (sequence [encode .x8 .x8 704 64, encode .x8 .x8 736 96]) else encodeDER),
    commit 704 size, .asm endWork]) (callees c)

/-- Public verification: variable branches only on public point/signature data.
The policy accepts high-S by default (standard ECDSA, libp2p interoperability).
Set lowS=true for canonical-only verification. Signing K256 is always low-S.
Digest is exactly SHA256 output32; message hashing belongs to the caller. -/
def verifyArithmetic (c : Curve) : Part := .seq [
  digestScalar, op 3 96 96 608, op 7 160 96 96,
  op 3 32 32 608, op 3 32 32 160, op 3 32 32 544,
  op 3 128 64 608, op 3 128 128 160, op 3 128 128 544,
  op 9 384 128 192, basePoint c 192, op 9 288 32 192,
  op 8 288 288 384,
  .asm (isZero .x8 352 .x22), failWork (.ne .x22 .x0) 6,
  op 10 288 288 288, .asm (zeroWords .x8 640 4), op 4 288 288 640,
  .asm (equal .x8 288 64 .x22),
  .asm (block [.XORI .x22 .x22 1, .ADDI .x5 .x0 6, .MUL .x19 .x22 .x5])]

def verify (c : Curve) (compact : Bool := false) (lowS : Bool := false) : Except String SAsm.Stmt :=
  program (.seq [.asm descriptorCheck, .asm (inputCheck 16 (keyBytes c)),
    .asm (inputCheck 32 32), .asm (signatureCheck compact), .asm (buffersCheck 0),
    .asm beginWork, setupConstants c, parseSignature c compact lowS, peer c,
    verifyArithmetic c, .asm endWork]) (callees c)

end Libp2pAsm.Asm.Crypto.Weierstrass
