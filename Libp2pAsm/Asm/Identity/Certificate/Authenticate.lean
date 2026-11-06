import Libp2pAsm.Asm.Identity.Certificate.Signature
import Libp2pAsm.Asm.Identity.Certificate.Usage

namespace Libp2pAsm.Asm.Identity.Certificate
open Rv64 Crypto.Util Crypto.Link
open Crypto.Curve25519 (ptr)

private def preflight : SAsm.Stmt := sequence [baseCheck,
  block [.LD .x5 .x10 64, .ADDI .x7 .x0 (imm outputBytes)], reject (.ltu .x5 .x7) 5,
  block [.LD .x5 .x10 48, .ADDI .x7 .x0 39], reject (.ltu .x7 .x5) 25,
  block [.LD .x6 .x10 24, .ADDI .x7 .x0 1],
  .ite (.eq .x6 .x7) (reject (.eq .x5 .x0) 25) empty,
  Crypto.Quic.spans descriptorBytes stackBytes [Crypto.Quic.variableSpan 0 8,
    Crypto.Quic.variableSpan 40 48, Crypto.Quic.fixed 56 outputBytes,
    ⟨Crypto.Quic.field 72, workExpr⟩]]

private def validity : Part := .seq [
  .asm (block [.LD .x10 .x9 112, .LD .x11 .x9 120, .LD .x12 .x8 32]), checked 1 21,
  .asm (sequence [block [.LD .x5 .x9 160, .LD .x6 .x8 24], usageMask,
    require (.ne .x5 .x0) 22])]

def selfSignature : Part := .seq [
  .asm (sequence [spanArgs 40 544, spanArgs 96 560, spanArgs 0 576,
    block [.LD .x5 .x9 88, .SD .x9 .x5 592, .LD .x6 .x9 32, .ADDI .x7 .x0 3],
    .ite (.geu .x5 .x7) (block [.ADDI .x5 .x0 3]) empty,
    require (.eq .x5 .x6) 27]), signature 23]

private def hostKey : Part := .seq [
  .asm (sequence [block [.LD .x11 .x9 136, .LD .x7 .x8 104],
    require (.geu .x7 .x11) 29, debitLinear .x11 1024 100000,
    block [.LD .x10 .x9 128, .ADD .x10 .x20 .x10, .LD .x11 .x9 136,
      .ADDI .x12 .x18 0, .ADDI .x13 .x19 0]]), checked 2 28,
  .asm (block [.SD .x9 .x11 600, .LD .x5 .x9 128, .ADD .x5 .x20 .x5,
    .ADD .x5 .x5 .x12, .SD .x9 .x5 608, .SD .x9 .x13 616,
    .SD .x9 .x5 544, .SD .x9 .x13 552, .ADDI .x7 .x0 2]),
  .asm (.ite (.eq .x11 .x7) (block [.ADDI .x11 .x0 5]) empty),
  .asm (sequence [block [.SD .x9 .x11 592], spanArgs 144 560,
    block (ptr .x22 .x9 2048),
    Crypto.Quic.writeBytes .x22 0 (Spec.Identity.Certificate.hostPrefix.map UInt8.toNat),
    block [.ADDI .x10 .x22 (imm Spec.Identity.Certificate.hostPrefix.length),
      .LD .x11 .x9 16, .ADD .x11 .x20 .x11, .LD .x12 .x9 24,
      .ADDI .x5 .x12 (imm Spec.Identity.Certificate.hostPrefix.length),
      .SD .x9 .x22 576, .SD .x9 .x5 584],
    copy .x10 .x11 .x12]), signature 24]

private def stage : Part := .seq [
  .asm (block [.LD .x10 .x9 600, .LD .x11 .x9 608, .LD .x12 .x9 616,
    .ADDI .x13 .x9 456, .ADDI .x14 .x0 40]), checked 3 28,
  .asm (sequence [block [.SD .x9 .x11 336,
    .LD .x5 .x9 600, .SD .x9 .x5 320, .LD .x12 .x9 616, .SD .x9 .x12 328,
    .LD .x5 .x9 32, .SD .x9 .x5 344, .LD .x5 .x9 40, .SD .x9 .x5 352,
    .LD .x5 .x9 48, .SD .x9 .x5 360, .LD .x5 .x9 56, .SD .x9 .x5 368,
    .LD .x5 .x9 64, .SD .x9 .x5 376, .LD .x5 .x9 72, .SD .x9 .x5 384,
    .LD .x5 .x9 80, .SD .x9 .x5 392, .SD .x9 .x21 400,
    .LD .x5 .x9 88, .SD .x9 .x5 408, .ADDI .x10 .x9 416, .LD .x11 .x9 608],
    copy .x10 .x11 .x12])]

private def expectedPeer : SAsm.Stmt := sequence [
  block [.LD .x12 .x8 48],
  .ite (.ne .x12 .x0) (sequence [
    block [.LD .x5 .x9 336], require (.eq .x5 .x12) 25,
    block [.LD .x10 .x8 40, .ADDI .x11 .x9 456, .ADDI .x13 .x0 0],
    .loop (.ne .x12 .x0) (block [.LBU .x5 .x10 0, .LBU .x6 .x11 0,
      .XOR .x5 .x5 .x6, .OR .x13 .x13 .x5,
      .ADDI .x10 .x10 1, .ADDI .x11 .x11 1, .ADDI .x12 .x12 (-1)]),
    require (.eq .x13 .x0) 25]) empty]

private def publish : SAsm.Stmt := sequence [expectedPeer,
  block [.LD .x10 .x8 56, .ADDI .x11 .x9 320, .ADDI .x12 .x0 (imm outputBytes)],
  copy .x10 .x11 .x12, block [.ADDI .x10 .x0 0], cleanup]

/-- Actual internal certificate authentication. Descriptor/ownership contract is
documented in docs/certificate-auth.md. No structural view or identity is copied
to caller output until every cryptographic and peer-binding check succeeds. -/
def authenticate : Except String SAsm.Stmt := do
  program (.seq [.asm preflight, .asm setup, parser, validity, selfSignature,
    hostKey, stage, .asm publish]) (← verifyCallees)

end Libp2pAsm.Asm.Identity.Certificate
