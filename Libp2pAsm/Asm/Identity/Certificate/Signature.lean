import Libp2pAsm.Asm.Identity.Certificate.Common

namespace Libp2pAsm.Asm.Identity.Certificate
open Rv64 Crypto.Util Crypto.Link

def hashMessage (code : Nat) : Part := .seq [
  .asm (sequence [block [.LD .x14 .x9 584], debitLinear .x14 1024 100000,
    block [.LD .x10 .x9 576, .LD .x11 .x9 584, .ADDI .x12 .x9 512,
      .ADDI .x13 .x18 0, .ADDI .x14 .x19 0, .ADDI .x15 .x9 640]]),
  checked 9 code]

def verifyEd (code : Nat) : Part := .seq [
  .asm (sequence [block [.LD .x14 .x9 584], debitLinear .x14 1024 16000000,
    block [.LD .x10 .x9 544, .LD .x11 .x9 552,
      .LD .x12 .x9 576, .LD .x13 .x9 584,
      .LD .x14 .x9 560, .LD .x15 .x9 568,
      .ADDI .x16 .x18 0, .ADDI .x17 .x19 0]]), checked 4 code]

def ecDescriptor : SAsm.Stmt := block [
  .LD .x5 .x9 544, .SD .x9 .x5 192, .LD .x5 .x9 552, .SD .x9 .x5 200,
  .ADDI .x5 .x9 512, .SD .x9 .x5 208, .ADDI .x5 .x0 32, .SD .x9 .x5 216,
  .LD .x5 .x9 560, .SD .x9 .x5 224, .LD .x5 .x9 568, .SD .x9 .x5 232,
  .SD .x9 .x0 240, .SD .x9 .x0 248, .SD .x9 .x18 256, .SD .x9 .x19 264,
  .ADDI .x5 .x9 640, .SD .x9 .x5 272, .ADDI .x10 .x9 176]

def verifyEc (callee code : Nat) : Part := .seq [hashMessage code,
  .asm (sequence [debitFixed 32000000, ecDescriptor]), checked callee code]

/-- Mirrors the frozen RSA estimator without narrowing its u64 operands.
The arithmetic-size gate is the frozen RSA ABI's domain, not a policy cap. -/
def rsaBudget : SAsm.Stmt := sequence [
  block [.LD .x11 .x9 64, .LD .x12 .x9 80],
  block (load .x7 Crypto.RSA.arithmeticByteLimit),
  require (.geu .x7 .x11) 29, require (.geu .x7 .x12) 29,
  block [.ADDI .x16 .x11 3, .SRLI .x16 .x16 2,
    .ADDI .x15 .x16 1, .MUL .x15 .x15 .x15, .SLLI .x15 .x15 6,
    .SLLI .x13 .x12 4, .ADDI .x13 .x13 4, .MUL .x15 .x15 .x13,
    .MUL .x13 .x16 .x16, .SLLI .x13 .x13 12, .ADD .x15 .x15 .x13,
    .ADDI .x13 .x11 31, .SRLI .x13 .x13 5, .ADDI .x13 .x13 2],
  block (load .x7 50000 ++ [.MUL .x13 .x13 .x7, .ADD .x15 .x15 .x13,
    .ADDI .x7 .x0 1000, .MUL .x13 .x11 .x7, .ADD .x15 .x15 .x13] ++
    load .x7 100000 ++ [.ADD .x15 .x15 .x7, .SD .x9 .x15 288]), debit .x15]

def rsaDescriptor : SAsm.Stmt := sequence [spanArgs 56 176, spanArgs 72 192,
  block [.LD .x5 .x9 560, .SD .x9 .x5 208, .LD .x5 .x9 568, .SD .x9 .x5 216,
    .ADDI .x5 .x9 512, .SD .x9 .x5 224, .ADDI .x5 .x0 32, .SD .x9 .x5 232,
    .SD .x9 .x18 240, .SD .x9 .x19 248, .ADDI .x5 .x9 640, .SD .x9 .x5 256,
    .LD .x5 .x8 112, .SD .x9 .x5 264, .LD .x5 .x8 120, .SD .x9 .x5 272,
    .LD .x5 .x8 128, .SD .x9 .x5 280,
    .ADDI .x5 .x0 288, .SD .x9 .x5 296, .ADDI .x10 .x9 176]]

def verifyRsa (callee code : Nat) : Part := .seq [hashMessage code,
  .asm (sequence [rsaBudget, rsaDescriptor]), checked callee code]

/-- Dispatch codes1=Ed,2=P256,3=RSA-PKCS1,4=RSA-PSS,5=K256.
Key/scheme binding is checked by the owning certificate/CV entry. -/
def signature (code : Nat) : Part :=
  [(1, verifyEd code), (2, verifyEc 5 code), (3, verifyRsa 7 code),
    (4, verifyRsa 8 code), (5, verifyEc 6 code)].foldr
    (fun (kind, body) rest => .seq [
      .asm (block [.LD .x5 .x9 592, .ADDI .x7 .x0 (imm kind)]),
      .ite (.eq .x5 .x7) body rest]) (.asm (fail 27))

def verifyCallees : Except String (List Part) := do
  return [.asm (← X509.certificate), .asm Time.validity,
    .asm (← PublicKey.decode), .asm PublicKey.peerId,
    .asm (← Crypto.Curve25519.Verify.verify), .asm (← Crypto.Weierstrass.verify .p256),
    .asm (← Crypto.Weierstrass.verify .secp256k1), .asm (← Crypto.RSA.rsaPkcs1Sha256),
    .asm (← Crypto.RSA.rsaPssRsaeSha256), .asm (Crypto.Whole.hash .sha256)]

end Libp2pAsm.Asm.Identity.Certificate
