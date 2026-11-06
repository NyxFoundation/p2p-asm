import Libp2pAsm.Asm.Crypto.Weierstrass.Ecdsa

namespace Libp2pAsm.Tests.Weierstrass
open Rv64 Asm.Crypto Asm.Crypto.Util Asm.Crypto.Link Asm.Crypto.Weierstrass
open Spec.Crypto.Weierstrass (Curve)

/-- Test-only composition: validates DER/range and returns compact, no ECDSA.
Uses the exact production parser. No new runtime primitive is defined. -/
def parseFragment (c : Curve) : Except String SAsm.Stmt := program (.seq [
  .asm descriptorCheck, .asm (signatureCheck false), .asm (buffersCheck 64),
  .asm beginWork, parseSignature c false false,
  .asm (encode .x8 .x8 704 64), .asm (encode .x8 .x8 736 96),
  commit 704 64, .asm endWork]) (callees c)

/-- Test-only encoding fragment uses production fixed-access DER encoder. -/
def encodeFragment (c : Curve) : Except String SAsm.Stmt := program (.seq [
  .asm enter, .asm (block [.ADDI .x8 .x13 0, .ADDI .x9 .x12 0]),
  .asm (decode .x8 .x10 64 0), .asm (decode .x8 .x11 96 0), encodeDER,
  .asm (block [.ADDI .x10 .x9 0, .ADDI .x11 .x8 704, .ADDI .x12 .x0 80]),
  .asm (copy .x10 .x11 .x12), .asm (zeroWords .x8 0 128),
  .asm (block [.ADDI .x10 .x0 0]), .asm leave]) (callees c)

def nonceFragment (c : Curve) : Except String SAsm.Stmt := program (.seq [
  .asm descriptorCheck, .asm (inputCheck 0 32), .asm (inputCheck 32 32),
  .asm (buffersCheck 32 true), .asm beginWork, setupConstants c, secretScalar c,
  nonce c, .asm (encode .x8 .x8 704 128), commit 704 32, .asm endWork]) (callees c)

/-- Exact signer failure/commit path with injected rare states, test only.
Secret source96 bytes: nonce32,r32,s32. These states are otherwise infeasible
to deliberately obtain from HMAC. No production signer accepts injected state. -/
def failureFragment (c : Curve) : Except String SAsm.Stmt := program (.seq [
  .asm descriptorCheck, .asm (inputCheck 0 96), .asm (buffersCheck 64),
  .asm beginWork, setupConstants c,
  .asm (block [.LD .x11 .x9 0]), .asm (decode .x8 .x11 128 0),
  .asm (decode .x8 .x11 64 32), .asm (decode .x8 .x11 96 64),
  acceptCandidate c, signatureStatus,
  .asm (encode .x8 .x8 704 64), .asm (encode .x8 .x8 736 96),
  commit 704 64, .asm endWork]) (callees c)

end Libp2pAsm.Tests.Weierstrass
