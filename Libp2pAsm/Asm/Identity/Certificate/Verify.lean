import Libp2pAsm.Asm.Identity.Certificate.Signature

namespace Libp2pAsm.Asm.Identity.Certificate
open Rv64 Crypto.Util Crypto.Link
open Crypto.Curve25519 (ptr)

def cvBytes (role : Nat) : List Nat :=
  List.replicate 64 32 ++ (Spec.Identity.Certificate.roleContext role).map UInt8.toNat ++ [0]

private def preflight : SAsm.Stmt := sequence [baseCheck,
  block [.LD .x5 .x10 152, .ADDI .x7 .x0 32], reject (.ne .x5 .x7) 1,
  Crypto.Quic.spans descriptorBytes stackBytes [Crypto.Quic.variableSpan 0 8,
    Crypto.Quic.fixed 144 32, Crypto.Quic.variableSpan 160 168,
    ⟨Crypto.Quic.field 72, workExpr⟩]]

def cvBuild : SAsm.Stmt := sequence [block (ptr .x22 .x9 2048),
  block [.LD .x5 .x8 24, .ADDI .x7 .x0 1],
  .ite (.eq .x5 .x7) (Crypto.Quic.writeBytes .x22 0 (cvBytes 1))
    (Crypto.Quic.writeBytes .x22 0 (cvBytes 2)),
  block [.ADDI .x10 .x22 98, .LD .x11 .x8 144, .ADDI .x12 .x0 32],
  copy .x10 .x11 .x12,
  block [.SD .x9 .x22 576, .ADDI .x5 .x0 130, .SD .x9 .x5 584]]

private def binding : SAsm.Stmt := sequence [
  block [.LD .x5 .x9 32, .LD .x6 .x8 176, .ADDI .x7 .x0 1],
  .ite (.eq .x5 .x7)
    (sequence [block (load .x7 0x0807), require (.eq .x6 .x7) 27])
    (.ite (.eq .x5 .x0) (fail 27) (sequence [block [.ADDI .x7 .x0 2],
      .ite (.eq .x5 .x7)
        (sequence [block [.ADDI .x7 .x0 0x0403], require (.eq .x6 .x7) 27])
        (sequence [block [.ADDI .x7 .x0 3], require (.eq .x5 .x7) 27,
          block (load .x7 0x0804), require (.eq .x6 .x7) 27,
          block [.ADDI .x5 .x0 4]])])),
  block [.SD .x9 .x5 592]]

/-- Independently parses the raw certificate to bind supported CV scheme to its
actual subject key. Does not claim certificate authentication or TLS completion. -/
def verifyCV : Except String SAsm.Stmt := do
  program (.seq [.asm preflight, .asm setup, parser,
    .asm (sequence [binding, cvBuild, spanArgs 40 544,
      block [.LD .x5 .x8 160, .SD .x9 .x5 560, .LD .x5 .x8 168, .SD .x9 .x5 568]]),
    signature 23, .asm (sequence [block [.ADDI .x10 .x0 0], cleanup])]) (← verifyCallees)

end Libp2pAsm.Asm.Identity.Certificate
