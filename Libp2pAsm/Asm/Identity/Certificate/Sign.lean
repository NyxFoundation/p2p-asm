import Libp2pAsm.Asm.Identity.Certificate.Verify

namespace Libp2pAsm.Asm.Identity.Certificate
open Rv64 Crypto.Util Crypto.Link

private def preflight : SAsm.Stmt := sequence [Crypto.Quic.descriptor descriptorBytes,
  block [.LD .x5 .x10 8, .ADDI .x7 .x0 32], reject (.ne .x5 .x7) 1,
  block [.LD .x5 .x10 152], reject (.ne .x5 .x7) 1, roleCheck,
  block [.LD .x5 .x10 64, .ADDI .x7 .x0 64], reject (.ltu .x5 .x7) 5,
  block (workExpr .x12 ++ [.LD .x13 .x10 80]), reject (.ltu .x13 .x12) 5,
  block [.LD .x5 .x10 136, .ADDI .x7 .x0 (imm stackBytes)], reject (.ltu .x5 .x7) 5,
  Crypto.Quic.alignedField 72,
  Crypto.Quic.spans descriptorBytes stackBytes [Crypto.Quic.fixed 0 32,
    Crypto.Quic.fixed 144 32, Crypto.Quic.fixed 56 64, ⟨Crypto.Quic.field 72, workExpr⟩]]

/-- Descriptor shares role24,seed0/8,out56/64,work72/80,budget96,stack136,
transcript144/152 with verifyCV. The remaining descriptor fields are unused.
Only an owned, fresh per-connection Ed25519 seed belongs here. Output64 bytes. -/
def signCV : Except String SAsm.Stmt := do
  program (.seq [.asm preflight, .asm setup, .asm (debitFixed 14000000),
    .asm cvBuild,
    .asm (block [.ADDI .x10 .x20 0, .ADDI .x11 .x0 32,
      .LD .x12 .x9 576, .ADDI .x13 .x0 130, .ADDI .x14 .x9 320,
      .ADDI .x15 .x0 64, .ADDI .x16 .x18 0, .ADDI .x17 .x19 0]),
    checked 0 30,
    .asm (sequence [block [.LD .x10 .x8 56, .ADDI .x11 .x9 320, .ADDI .x12 .x0 64],
      copy .x10 .x11 .x12, block [.ADDI .x10 .x0 0], cleanup])])
    [.asm (← Crypto.Curve25519.Ed25519.sign)]

end Libp2pAsm.Asm.Identity.Certificate
