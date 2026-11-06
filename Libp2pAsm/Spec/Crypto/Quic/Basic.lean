import Libp2pAsm.Spec.Crypto.HKDF
import Libp2pAsm.Spec.Crypto.TlsKdf
import Libp2pAsm.Spec.Crypto.GCM.Basic

/-! Independent RFC 9001 §§5/6 and RFC 9000 Appendix A.3 reference.
No transport parser, packet spaces, replay policy or key-phase state. -/
namespace Libp2pAsm.Spec.Crypto.Quic

inductive Error where
  | length | number | header | sample | authentication | crypto
  deriving BEq, DecidableEq, Repr

def initialSalt : Bytes := [0x38,0x76,0x2c,0xf7,0xf5,0x59,0x34,0xb3,0x4d,0x17,
  0x9a,0xe6,0xa4,0xc8,0x0c,0xad,0xcc,0xbb,0x7f,0x0a]
def retryKey : Array UInt8 := #[0xbe,0x0c,0x69,0x0b,0x9f,0x66,0x57,0x5a,
  0x1d,0x76,0x6b,0x54,0xe3,0x68,0xc8,0x4e]
def retryNonce : Array UInt8 := #[0x46,0x15,0x99,0xd3,0x5d,0x63,0x2b,0xf2,0x23,0x98,0x25,0xbb]

def expandLabel (secret : Bytes) (label : String) (n : Nat) : Except Error Bytes := do
  if secret.length != 32 then throw .length
  let info ← (TlsKdf.encodeLabel n label.toUTF8.data.toList []).mapError (fun _ => .crypto)
  (HKDF.expand secret info n).mapError (fun _ => .crypto)

/-- Packed key[16] || IV[12] || HP[16]. -/
def packetKeys (secret : Bytes) : Except Error Bytes := do
  return (← expandLabel secret "quic key" 16) ++ (← expandLabel secret "quic iv" 12) ++
    (← expandLabel secret "quic hp" 16)

/-- Update emits next secret[32] || key[16] || IV[12]; HP is deliberately absent.
The caller retains the original HP key for the connection. -/
def update (secret : Bytes) : Except Error Bytes := do
  let next ← expandLabel secret "quic ku" 32
  return next ++ (← expandLabel next "quic key" 16) ++ (← expandLabel next "quic iv" 12)

/-- Primitive CID domain is 0..20, independent of Initial packet validation. -/
def initial (dcid : Bytes) : Except Error Bytes := do
  if dcid.length > 20 then throw .length
  let secret ← (HKDF.extract (some initialSalt) dcid).mapError (fun _ => .crypto)
  let client ← expandLabel secret "client in" 32
  let server ← expandLabel secret "server in" 32
  return secret ++ client ++ server ++ (← packetKeys client) ++ (← packetKeys server)

def nonceWord (iv : BitVec 96) (pn : BitVec 64) : BitVec 96 := iv ^^^ pn.zeroExtend 96

def nonce (iv : Array UInt8) (pn : Nat) : Except Error (Array UInt8) := do
  if pn ≥ 2^62 then throw .number
  if iv.size != 12 then throw .length
  let padded := (Sha2.encodeBE 12 pn).toArray
  return iv.zipWith (· ^^^ ·) padded

/-- expected=largest+1, including 2^62 at exhaustion; expected=0 before receipt.
Natural addition in the first comparison avoids unsigned subtraction underflow.
Candidates outside the 62-bit domain are rejected, never wrapped. -/
def reconstruct (expected truncated bytes : Nat) : Except Error Nat := do
  if expected > 2^62 || bytes < 1 || bytes > 4 then throw .number
  let window := 2^(8*bytes)
  if truncated ≥ window then throw .number
  let candidate := expected / window * window + truncated
  let result := if candidate + window/2 ≤ expected && candidate < 2^62-window then
      candidate+window
    else if candidate > expected+window/2 && candidate ≥ window then candidate-window
    else candidate
  if result ≥ 2^62 then throw .number
  return result

def retryTag (odcid retry : Array UInt8) : Except Error (Array UInt8) := do
  if odcid.size > 20 then throw .length
  (GCM.seal retryKey retryNonce (#[odcid.size.toUInt8] ++ odcid ++ retry) #[]).mapError
    (fun _ => .crypto)

def retryCheck (odcid packet : Array UInt8) : Except Error Unit := do
  if packet.size < 16 then throw .length
  let tag ← retryTag odcid (packet.extract 0 (packet.size-16))
  if tag != packet.extract (packet.size-16) packet.size then throw .authentication

end Libp2pAsm.Spec.Crypto.Quic
