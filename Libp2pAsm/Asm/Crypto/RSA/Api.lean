import Libp2pAsm.Asm.Crypto.RSA.EMSA

namespace Libp2pAsm.Asm.Crypto.RSA
open Rv64 Util Link

/-- Raw public verification entry. a0=128-byte descriptor; a0=status on return.
Full ABI, ownership, mapping, timing and cleanup contract: Tests/RSA/README.md.
PKCS#1 v1.5 is certificate-only; PSS supports certificates/CertificateVerify.
These routines never generate/sign with RSA and never return key material. -/
def verify (usePSS : Bool) : Except String SAsm.Stmt := Link.program (.seq [
  .asm preflight, .asm beginWork, .asm keyContent, .asm loadOperands,
  precompute, exponentiate, if usePSS then pss else .asm pkcs,
  .asm (block [.ADDI .x10 .x0 0]), .asm endWork])
  [.asm montgomery, .asm doubleMod, .asm (Whole.body .sha256)]

def rsaPkcs1Sha256 : Except String SAsm.Stmt := verify false
def rsaPssRsaeSha256 : Except String SAsm.Stmt := verify true

end Libp2pAsm.Asm.Crypto.RSA
