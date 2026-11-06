import Libp2pAsm.Spec.Tls.Basic
import Libp2pAsm.Spec.Crypto.HKDF
import Libp2pAsm.Spec.Crypto.TlsKdf

/-! RFC 8446 sections 4.4.1, 4.4.4 and 7.1; SHA256, full (EC)DHE only.
No PSK, early data, resumption, record encryption, or authentication decision.
Digest arguments MUST include the specified complete handshake messages,
including their four-byte headers. The caller owns transcript storage. -/
namespace Libp2pAsm.Spec.Tls.Schedule

def hash (transcript : Bytes) (limit : Nat) : Except Error Bytes := do
  if transcript.size > limit then throw .limit
  return (← Crypto.SHA256.hash transcript.toList |>.mapError (fun _ => .crypto)).toArray

def expandLabel (secret : Bytes) (label : String) (context : Bytes) : Except Error Bytes := do
  if secret.size != 32 then throw .malformed
  let info ← Crypto.TlsKdf.encodeLabel 32 label.toUTF8.data.toList context.toList
    |>.mapError (fun _ => Error.malformed)
  return (← Crypto.HKDF.expand secret.toList info 32 |>.mapError (fun _ => .crypto)).toArray

def extract (salt ikm : Bytes) : Except Error Bytes := do
  return (← Crypto.HKDF.extract (some salt.toList) ikm.toList
    |>.mapError (fun _ => Error.crypto)).toArray

structure Handshake where
  early : Bytes
  earlyDerived : Bytes
  handshake : Bytes
  client : Bytes
  server : Bytes
  handshakeDerived : Bytes
  master : Bytes
  deriving BEq, Repr

def Handshake.bytes (s : Handshake) : Bytes :=
  s.early ++ s.earlyDerived ++ s.handshake ++ s.client ++ s.server ++ s.handshakeDerived ++ s.master

/-- `helloDigest` is Hash(ClientHello ... ServerHello), including HRR rewrite.
Both X25519 and P256 ECDHE shared-secret encodings have 32 bytes. -/
def handshake (shared helloDigest : Bytes) : Except Error Handshake := do
  if shared.size != 32 || helloDigest.size != 32 then throw .malformed
  let zero := Array.replicate 32 0
  let emptyHash ← hash #[] 0
  let early ← extract zero zero
  let earlyDerived ← expandLabel early "derived" emptyHash
  let hs ← extract earlyDerived shared
  let client ← expandLabel hs "c hs traffic" helloDigest
  let server ← expandLabel hs "s hs traffic" helloDigest
  let handshakeDerived ← expandLabel hs "derived" emptyHash
  let master ← extract handshakeDerived zero
  return ⟨early, earlyDerived, hs, client, server, handshakeDerived, master⟩

/-- Hash(ClientHello ... server Finished), INCLUDING server Finished. -/
def application (master serverFinishedDigest : Bytes) : Except Error Bytes := do
  if master.size != 32 || serverFinishedDigest.size != 32 then throw .malformed
  return (← expandLabel master "c ap traffic" serverFinishedDigest) ++
    (← expandLabel master "s ap traffic" serverFinishedDigest)

/-- Hash through the sender's CertificateVerify, EXCLUDING this Finished.
For the client this includes server Finished and the client's auth flight. -/
def finished (traffic beforeFinishedDigest : Bytes) : Except Error Bytes := do
  if traffic.size != 32 || beforeFinishedDigest.size != 32 then throw .malformed
  let key ← expandLabel traffic "finished" #[]
  let verify ← Crypto.HMAC.sha256 key.toList beforeFinishedDigest.toList
    |>.mapError (fun _ => Error.crypto)
  return key ++ verify.toArray

/-- Replace ClientHello1 with message_hash(254, uint24(32), Hash(CH1)).
Caller concatenates this with HRR, CH2, SH, ...; this function does not insert
record headers, hash a prehashed digest, or retain transcript state. -/
def messageHash (clientHello1 : Bytes) (limit : Nat) : Except Error Bytes := do
  return #[254,0,0,32] ++ (← hash clientHello1 limit)

def full (shared helloDigest serverFinishedDigest : Bytes) : Except Error Bytes := do
  let hs ← handshake shared helloDigest
  return hs.bytes ++ (← application hs.master serverFinishedDigest)

end Libp2pAsm.Spec.Tls.Schedule
