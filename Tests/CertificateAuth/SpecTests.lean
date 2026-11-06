import Libp2pAsm.Spec.Identity.Certificate.Issue
import Libp2pAsm.Spec.Identity.Certificate.Verify

namespace Libp2pAsm.Tests.CertificateAuth
open Spec.Identity.Certificate

example : (cvMessage 1 (List.replicate 32 0)).map List.length = .ok 130 := by rfl
example : (cvMessage 2 (List.replicate 32 0)).map List.length = .ok 130 := by rfl
example : cvMessage 0 (List.replicate 32 0) = .error .role := by rfl
example : cvMessage 1 [] = .error .length := by rfl
example : (cvMessage 1 (List.replicate 32 1)).toOption !=
    (cvMessage 2 (List.replicate 32 1)).toOption := by decide
example : schemeMatches 1 0x0807 = true := by decide
example : schemeMatches 2 0x0403 = true := by decide
example : schemeMatches 3 0x0804 = true := by decide
example : schemeMatches 3 0x0401 = false := by decide
example : schemeMatches 1 0x0403 = false := by decide
example : schemeMatches 2 0x0807 = false := by decide

end Libp2pAsm.Tests.CertificateAuth
