import Libp2pAsm.Spec.Identity.X509.Algorithm
import Libp2pAsm.Asm.Identity.X509.Algorithm

namespace Libp2pAsm.Tests.CertificateAlgorithms

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL: {name}")

def run : IO Unit := do
  let ed : List UInt8 := [0x30, 5, 6, 3, 43, 101, 112]
  check "should recognize Ed25519 AlgorithmIdentifier with absent parameters"
    (match Spec.Identity.X509.signatureAlgorithm ed with | .ok 1 => true | _ => false)
  check "should reject Ed25519 NULL parameters"
    (match Spec.Identity.X509.signatureAlgorithm [0x30, 7, 6, 3, 43, 101, 112, 5, 0] with
      | .error .algorithm => true | _ => false)
  check "should reject a trailing algorithm node"
    (match Spec.Identity.X509.signatureAlgorithm (ed ++ [5, 0]) with
      | .error .malformed => true | _ => false)
  IO.println "PASS: should validate X509 signature and public-key AlgorithmIdentifiers"

end Libp2pAsm.Tests.CertificateAlgorithms
