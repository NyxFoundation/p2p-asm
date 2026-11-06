import Libp2pAsm.Spec.Identity.Certificate.Types
import Libp2pAsm.Spec.Crypto.Curve25519.Ed25519
import Libp2pAsm.Spec.Crypto.Weierstrass.Ecdsa
import Libp2pAsm.Spec.Crypto.RSA.EMSA

namespace Libp2pAsm.Spec.Identity.Certificate
open Crypto

def hash (message : List UInt8) : Except Error (List UInt8) :=
  SHA256.hash message |>.mapError (fun _ => .length)

def ecVerify (curve : Weierstrass.Curve) (key message signature : List UInt8) : Bool :=
  match Weierstrass.decodePoint curve (curve == .secp256k1) key,
      Weierstrass.parseDER curve false signature, hash message with
  | some point, some sig, .ok digest => Weierstrass.verify curve false point digest sig
  | _, _, _ => false

def hostVerify (kind : Nat) (key message signature : List UInt8) : Bool :=
  if kind == 1 then (Curve25519.Ed25519.verify key message signature).isOk
  else kind == 2 && ecVerify .secp256k1 key message signature

/-- Exact source spans are hashed; ASN.1 parsing alone never establishes trust. -/
def subjectVerify (policy : Policy) (raw : List UInt8) (key : X509.PublicKeyView)
    (kind : Nat) (message signature : List UInt8) : Bool :=
  if kind == 1 then key.kind == 1 && hostVerify 1 (key.data.bytes raw) message signature
  else if kind == 2 then key.kind == 2 && ecVerify .p256 (key.data.bytes raw) message signature
  else if (kind == 3 || kind == 4) && key.kind == 3 then
    let modulus := key.modulus.bytes raw
    let exponent := key.exponent.bytes raw
    modulus.length ≤ policy.modulusBytes && exponent.length ≤ policy.exponentBytes &&
      match hash message with
      | .error _ => false
      | .ok digest => RSA.verify (if kind == 3 then .pkcs1Sha256 else .pssRsaeSha256)
          policy.minimumRsaBits modulus exponent digest signature
  else false

def authenticate (policy : Policy) (chain : List (List UInt8)) (role : Nat)
    (utcNs : Int) (expectedPeer : List UInt8) : Except Error Authenticated := do
  if role != 1 && role != 2 then throw .role
  if role == 1 && expectedPeer.isEmpty then throw .peer
  let [raw] := chain | throw .length
  if raw.length > policy.certificateBytes then throw .resource
  let cert ← X509.certificate raw |>.mapError (fun _ => .parser)
  let _ ← Time.validity cert.notBefore cert.notAfter utcNs |>.mapError (fun _ => .time)
  if cert.usage &&& role == 0 then throw .usage
  unless subjectVerify policy raw cert.key cert.signatureKind (cert.tbs.bytes raw)
      (cert.signature.bytes raw) do throw .selfSignature
  let encoded := cert.hostKey.bytes raw
  if encoded.length > policy.hostPublicKeyBytes then throw .resource
  let host ← PublicKey.decode encoded |>.mapError (fun _ => .key)
  let key := (encoded.drop host.offset).take host.length
  unless hostVerify host.kind key (hostPrefix ++ cert.spki.bytes raw)
      (cert.hostSignature.bytes raw) do throw .hostSignature
  let id ← PublicKey.peerId host.kind key |>.mapError (fun _ => .key)
  if id.isEmpty || (!expectedPeer.isEmpty && id != expectedPeer) then throw .peer
  return ⟨host.kind, key, id, cert⟩

/-- Verifies possession of the exact certificate subject key, without claiming
that the caller completed certificate authentication or TLS Finished. -/
def verifyCV (policy : Policy) (raw : List UInt8) (scheme role : Nat)
    (transcript signature : List UInt8) : Except Error Unit := do
  let message ← cvMessage role transcript
  if raw.length > policy.certificateBytes then throw .resource
  let cert ← X509.certificate raw |>.mapError (fun _ => .parser)
  unless schemeMatches cert.key.kind scheme do throw .scheme
  let kind := if cert.key.kind == 3 then 4 else cert.key.kind
  unless subjectVerify policy raw cert.key kind message signature do throw .selfSignature

def signCV (seed : List UInt8) (role : Nat) (transcript : List UInt8) :
    Except Error (List UInt8) := do
  let message ← cvMessage role transcript
  Curve25519.Ed25519.sign seed message |>.mapError (fun _ => .signing)

end Libp2pAsm.Spec.Identity.Certificate
