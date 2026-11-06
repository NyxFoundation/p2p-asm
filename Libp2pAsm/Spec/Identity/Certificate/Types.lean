import Libp2pAsm.Spec.Identity.X509.Certificate
import Libp2pAsm.Spec.Identity.PublicKey

namespace Libp2pAsm.Spec.Identity.Certificate

inductive Error where
  | length | range | capacity | parser | time | usage | selfSignature
  | hostSignature | peer | role | scheme | key | resource | signing
  deriving BEq, DecidableEq, Repr

def Error.code : Error → Nat
  | .length => 1 | .range => 4 | .capacity => 5 | .parser => 20 | .time => 21
  | .usage => 22 | .selfSignature => 23 | .hostSignature => 24 | .peer => 25
  | .role => 26 | .scheme => 27 | .key => 28 | .resource => 29 | .signing => 30

/-- Resource/policy values come from the caller's Limits, never local defaults. -/
structure Policy where
  certificateBytes : Nat
  hostPublicKeyBytes : Nat
  modulusBytes : Nat
  exponentBytes : Nat
  minimumRsaBits : Nat
  deriving Repr

/-- Internal result only. TLS Finished is an additional caller-owned gate.
The raw certificate must remain immutable while its subject-key views are used. -/
structure Authenticated where
  hostKind : Nat
  hostKey : List UInt8
  peerId : List UInt8
  certificate : X509.Certificate
  deriving Repr

def hostPrefix : List UInt8 := "libp2p-tls-handshake:".toUTF8.data.toList

def roleContext (role : Nat) : List UInt8 :=
  (if role == 1 then "TLS 1.3, server CertificateVerify"
   else "TLS 1.3, client CertificateVerify").toUTF8.data.toList

def cvMessage (role : Nat) (digest : List UInt8) : Except Error (List UInt8) := do
  if role != 1 && role != 2 then throw .role
  if digest.length != 32 then throw .length
  return List.replicate 64 32 ++ roleContext role ++ [0] ++ digest

def schemeMatches (keyKind scheme : Nat) : Bool :=
  (keyKind == 1 && scheme == 0x0807) || (keyKind == 2 && scheme == 0x0403) ||
    (keyKind == 3 && scheme == 0x0804)

end Libp2pAsm.Spec.Identity.Certificate
