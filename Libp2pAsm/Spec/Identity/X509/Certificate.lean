import Libp2pAsm.Spec.Identity.X509.Extensions

namespace Libp2pAsm.Spec.Identity.X509

structure Certificate where
  tbs : Span
  spki : Span
  key : PublicKeyView
  signatureKind : Nat
  signature : Span
  notBefore : Int
  notAfter : Int
  hostKey : Span
  hostSignature : Span
  usage : Nat
  deriving Repr

private def tbsPrefix (bytes : List UInt8) (tbs : Node) : Except Error (Nat × Cursor) := do
  let (version, cursor) ← expect bytes tbs.children 0xa0
  let (value, done) ← expect bytes version.children 2
  finished done
  if value.content.bytes bytes != [2] then throw .malformed
  let (serial, cursor) ← expect bytes cursor 2
  let _ ← unsignedInteger bytes serial
  if serial.content.length > 20 then throw .malformed
  let (algorithm, cursor) ← expect bytes cursor 48
  let kind ← signatureAlgorithm (algorithm.raw.bytes bytes) |>.mapError (fun _ => .algorithm)
  let (issuer, cursor) ← expect bytes cursor 48
  name bytes issuer
  return (kind, cursor)

private def body (bytes : List UInt8) (tbs : Node) : Except Error Certificate := do
  let (kind, cursor) ← tbsPrefix bytes tbs
  let (valid, cursor) ← expect bytes cursor 48
  let (first, last) ← validity bytes valid
  let (subject, cursor) ← expect bytes cursor 48
  name bytes subject
  let (spki, cursor) ← expect bytes cursor 48
  let key ← publicKey bytes spki
  if (kind == 1 && key.kind != 1) || (kind == 2 && key.kind != 2) ||
      (kind ≥ 3 && key.kind != 3) then throw .algorithm
  let (ext, done) ← expect bytes cursor 0xa3
  finished done
  let info ← extensions bytes ext
  let some (hostKey, hostSignature) := info.identity | throw .missingIdentity
  return ⟨tbs.raw, spki.raw, key, kind, ⟨0, 0⟩, first, last, hostKey, hostSignature,
    if info.keyUsage then info.extendedUsage else 0⟩

/-- One v3 libp2p certificate. Deprecated unique IDs, extra root/TBS fields and
duplicate extensions are rejected. Parsing does not authenticate a peer. -/
def certificate (bytes : List UInt8) : Except Error Certificate := do
  let root ← whole bytes 48
  let (tbs, cursor) ← expect bytes root.children 48
  let parsed ← body bytes tbs
  let (algorithm, cursor) ← expect bytes cursor 48
  let kind ← signatureAlgorithm (algorithm.raw.bytes bytes) |>.mapError (fun _ => .algorithm)
  if kind != parsed.signatureKind then throw .algorithm
  let (signature, done) ← expect bytes cursor 3
  finished done
  let signature ← bitString bytes signature
  return { parsed with signature }

/-- Signed nanosecond wall-clock comparison avoids narrowing large certificate
years or accepting a fractional second after inclusive NotAfter. -/
def validAt (cert : Certificate) (utcNs : Int) : Bool :=
  cert.notBefore*1000000000 ≤ utcNs && utcNs ≤ cert.notAfter*1000000000

end Libp2pAsm.Spec.Identity.X509
