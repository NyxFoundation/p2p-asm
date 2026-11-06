import Libp2pAsm.Asm.Crypto.Weierstrass.Abi

namespace Libp2pAsm.Asm.Crypto.Weierstrass
open Rv64 Util Link
open Spec.Crypto.Weierstrass (Curve)

def keyBytes (c : Curve) : Nat := if c == .p256 then 65 else 33

/-- Public peer validation is complete before secret key bytes are accessed.
Output Q at192 in homogeneous Montgomery form. Status9=invalid public point.
Both curves have cofactor one: a finite on-curve point is in the prime-order group. -/
def loadX (c : Curve) : Part := .seq [
  .asm (block [.LD .x23 .x9 16, .LBU .x24 .x23 0]),
  (if c == .p256 then .seq [.asm (block [.ADDI .x5 .x0 4]), failWork (.ne .x24 .x5) 9]
   else .seq [.asm (block [.ANDI .x5 .x24 (-2), .ADDI .x6 .x0 2]),
     failWork (.ne .x5 .x6) 9]),
  .asm (decode .x8 .x23 192 1), .asm (canonical .x8 192 c.prime .x22),
  failWork (.eq .x22 .x0) 9, op 0 192 192 576,
  op 0 480 192 192, op 0 480 480 192,
  .asm (constant .x8 512 (c.a*2^256 % c.prime)), op 0 512 512 192,
  op 1 480 480 512, .asm (constant .x8 512 (c.b*2^256 % c.prime)), op 1 480 480 512]

def loadY (c : Curve) : Part := if c == .p256 then .seq [
  .asm (decode .x8 .x23 224 33), .asm (canonical .x8 224 c.prime .x22),
  failWork (.eq .x22 .x0) 9, op 0 224 224 576] else .seq [
  op 13 224 480 480, op 0 512 224 544,
  .asm (block [.LD .x5 .x8 512, .XOR .x5 .x5 .x24, .ANDI .x5 .x5 1,
    .SUB .x25 .x0 .x5]), .asm (zeroWords .x8 512 4), op 2 512 512 224,
  .asm (block [.ADDI .x10 .x8 224, .ADDI .x11 .x8 512, .ADDI .x12 .x8 224]),
  .asm (maskSelect .x10 .x11 .x12 .x25)]

def peer (c : Curve) : Part := .seq [loadX c, loadY c, op 0 512 224 224,
  .asm (equal .x8 512 480 .x22), failWork (.eq .x22 .x0) 9,
  .asm (constant .x8 256 (2^256 % c.prime))]

def encodeKey (c : Curve) : Part := .asm <| sequence [
  block (if c == .p256 then [.ADDI .x5 .x0 4, .SB .x8 .x5 704] else
    [.LD .x5 .x8 320, .ANDI .x5 .x5 1, .ADDI .x5 .x5 2, .SB .x8 .x5 704]),
  encode .x8 .x8 705 288,
  if c == .p256 then encode .x8 .x8 737 320 else empty]

/-- Caller supplies validated-domain random material; this API does not generate
entropy. Invalid d=0 or d>=n returns8 with unchanged output and identical trace. -/
def publicKey (c : Curve) : Except String SAsm.Stmt := program (.seq [
  .asm descriptorCheck, .asm (inputCheck 0 32), .asm (buffersCheck (keyBytes c)),
  .asm beginWork, setupConstants c, secretScalar c, basePoint c 192,
  op 9 288 0 192, op 10 288 288 288, encodeKey c,
  commit 704 (keyBytes c), .asm endWork]) (callees c)

/-- ECDH returns exactly 32 canonical big-endian bytes of the shared x coordinate.
P-256 peer input is the TLS 65-byte uncompressed SEC1 keyshare. -/
def ecdh (c : Curve := .p256) : Except String SAsm.Stmt := program (.seq [
  .asm descriptorCheck, .asm (inputCheck 0 32), .asm (inputCheck 16 (keyBytes c)),
  .asm (buffersCheck 32), .asm beginWork, setupConstants c, peer c, secretScalar c,
  op 9 288 0 192, op 10 288 288 288, .asm (encode .x8 .x8 704 288),
  commit 704 32, .asm endWork]) (callees c)

end Libp2pAsm.Asm.Crypto.Weierstrass
