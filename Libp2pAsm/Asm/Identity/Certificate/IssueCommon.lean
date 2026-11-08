import Libp2pAsm.Asm.Identity.Certificate.Common
import Libp2pAsm.Spec.Identity.Certificate.Issue

namespace Libp2pAsm.Asm.Identity.Certificate.Issue
open Rv64 Crypto.Util Crypto.Link
open Crypto.Curve25519 (ptr)

/-- Fixed construction extents, derived from Ed25519 SPKI, two bounded times,
one Ed25519/K256 host key, one <=72-byte host signature and two usage extensions.
These are representation sizes, not independently configurable resource limits. -/
def workSize : Nat := Certificate.workBytes 512

def preflight : SAsm.Stmt := sequence [Crypto.Quic.descriptor 192,
  block [.LD .x5 .x10 8, .ADDI .x7 .x0 32], reject (.ne .x5 .x7) 1,
  block [.LD .x5 .x10 56], reject (.ne .x5 .x7) 1,
  block [.LD .x5 .x10 88], reject (.ltu .x5 .x7) 5,
  block [.LD .x5 .x10 16, .ADDI .x5 .x5 (-1), .ADDI .x7 .x0 2],
  reject (.geu .x5 .x7) 28,
  block [.LD .x5 .x10 136, .ADDI .x7 .x0 48], reject (.ltu .x5 .x7) 5,
  block (load .x7 workSize ++ [.LD .x5 .x10 104]), reject (.ltu .x5 .x7) 5,
  block [.LD .x5 .x10 120, .ADDI .x7 .x0 (imm stackBytes)], reject (.ltu .x5 .x7) 5,
  Crypto.Quic.alignedField 96,
  Crypto.Quic.spans 192 stackBytes [Crypto.Quic.fixed 0 32, Crypto.Quic.fixed 48 32,
    Crypto.Quic.variableSpan 64 72, Crypto.Quic.fixed 80 32, Crypto.Quic.fixed 128 48,
    Crypto.Quic.fixed 96 workSize]]

def setup : SAsm.Stmt := sequence [enter,
  block [.ADDI .x8 .x10 0, .LD .x9 .x8 96, .LD .x20 .x8 0, .ADDI .x21 .x0 512],
  block (ptr .x18 .x9 4096 ++ load .x19 (workSize-4096) ++ load .x12 workSize),
  wipe .x9 .x12,
  block [.ADDI .x11 .x2 (-1440), .ADDI .x12 .x0 1440], wipe .x11 .x12,
  block [.LD .x5 .x8 112, .SD .x9 .x5 1152], constants, debitFixed 1000000]

def times : Part := .seq [
  .asm (sequence [block [.LD .x10 .x8 32, .LD .x11 .x8 40, .SLT .x5 .x11 .x10],
    require (.eq .x5 .x0) 21,
    block [.ADDI .x11 .x9 0, .ADDI .x12 .x0 17]]), checked 0 21,
  .asm (block [.SD .x9 .x11 1160, .LD .x10 .x8 40,
    .ADDI .x11 .x9 32, .ADDI .x12 .x0 17]), checked 0 21,
  .asm (block [.SD .x9 .x11 1168])]

def edPublic (secret : List Instr) (output : Nat) : Part := .seq [
  .asm (sequence [debitFixed 4000000,
    block (secret ++ [.ADDI .x11 .x0 32] ++ ptr .x12 .x9 output ++
      [.ADDI .x13 .x0 32, .ADDI .x14 .x18 0, .ADDI .x15 .x19 0])]), checked 1 30]

def ecDescriptor (out size : Nat) : SAsm.Stmt := block [
  .SD .x9 .x20 176, .ADDI .x5 .x0 32, .SD .x9 .x5 184,
  .ADDI .x5 .x9 576, .SD .x9 .x5 208, .ADDI .x5 .x0 32, .SD .x9 .x5 216,
  .ADDI .x5 .x9 (imm out), .SD .x9 .x5 240, .ADDI .x5 .x0 (imm size), .SD .x9 .x5 248,
  .SD .x9 .x18 256, .SD .x9 .x19 264, .ADDI .x5 .x9 640, .SD .x9 .x5 272,
  .ADDI .x10 .x9 176]

def hostPublic : Part := .seq [
  .asm (block [.LD .x5 .x8 16, .ADDI .x7 .x0 1]),
  .ite (.eq .x5 .x7) (edPublic [.ADDI .x10 .x20 0] 320)
    (.seq [.asm (sequence [debitFixed 16000000, ecDescriptor 320 33]), checked 3 30]),
  .asm (block [.LD .x10 .x8 16, .ADDI .x11 .x9 320, .ADDI .x12 .x10 31,
    .SD .x9 .x12 1176, .ADDI .x13 .x9 1208, .ADDI .x14 .x0 40]), checked 5 28,
  .asm (block [.SD .x9 .x11 1200])]

def spki : SAsm.Stmt := sequence [
  Crypto.Quic.writeBytes .x9 1280 ([48,42] ++
    (Spec.Identity.Certificate.edAlgorithm.map UInt8.toNat) ++ [3,33,0]),
  block [.ADDI .x10 .x9 1292, .ADDI .x11 .x9 360, .ADDI .x12 .x0 32],
  copy .x10 .x11 .x12,
  Crypto.Quic.writeBytes .x9 1344 (Spec.Identity.Certificate.hostPrefix.map UInt8.toNat),
  block [.ADDI .x10 .x9 (imm (1344 + Spec.Identity.Certificate.hostPrefix.length)),
    .ADDI .x11 .x9 1280, .ADDI .x12 .x0 44],
  copy .x10 .x11 .x12]

def edSign (secret : List Instr) (message length : List Instr) (output : Nat) : Part := .seq [
  .asm (sequence [debitFixed 14000000,
    block (secret ++ [.ADDI .x11 .x0 32] ++ message ++ length ++
      ptr .x14 .x9 output ++ [.ADDI .x15 .x0 64, .ADDI .x16 .x18 0, .ADDI .x17 .x19 0])]),
  checked 2 30]

def hostSign : Part := .seq [
  .asm (block [.LD .x5 .x8 16, .ADDI .x7 .x0 1]),
  .ite (.eq .x5 .x7) (.seq [
    edSign [.ADDI .x10 .x20 0] [.ADDI .x12 .x9 1344]
      [.ADDI .x13 .x0 (imm (44 + Spec.Identity.Certificate.hostPrefix.length))] 408,
    .asm (block [.ADDI .x5 .x0 64, .SD .x9 .x5 400])])
    (.seq [.asm (sequence [debitFixed 16000000,
      block [.ADDI .x10 .x9 1344,
        .ADDI .x11 .x0 (imm (44 + Spec.Identity.Certificate.hostPrefix.length)),
        .ADDI .x12 .x9 576,
        .ADDI .x13 .x18 0, .ADDI .x14 .x19 0, .ADDI .x15 .x9 640]]), checked 6 30,
      .asm (ecDescriptor 400 80), checked 4 30]),
  .asm (block [.LD .x5 .x9 400, .SD .x9 .x5 1184])]

def callees : Except String (List Part) := do
  return [.asm Time.encode, .asm (← Crypto.Curve25519.Ed25519.publicKey),
    .asm (← Crypto.Curve25519.Ed25519.sign),
    .asm (← Crypto.Weierstrass.publicKey .secp256k1),
    .asm (← Crypto.Weierstrass.sign .secp256k1), .asm PublicKey.peerId,
    .asm (Crypto.Whole.hash .sha256), .asm Codec.Der.encodeHeader]

end Libp2pAsm.Asm.Identity.Certificate.Issue
