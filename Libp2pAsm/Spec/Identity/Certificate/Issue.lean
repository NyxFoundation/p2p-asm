import Libp2pAsm.Spec.Identity.Certificate.Verify

namespace Libp2pAsm.Spec.Identity.Certificate
open Crypto

def tlv (tag : Nat) (body : List UInt8) : Except Error (List UInt8) := do
  let header ← Codec.Der.encodeHeader tag body.length |>.mapError (fun _ => .length)
  return header ++ body

def edAlgorithm : List UInt8 := [48,5,6,3,43,101,112]
def issuerName : List UInt8 := [48,17,49,15,48,13,6,3,85,4,3,12,6,108,105,98,112,50,112]
def identityOid : List UInt8 := [6,10,43,6,1,4,1,131,162,90,1,1]
def usageExtensions : List UInt8 :=
  [48,14,6,3,85,29,15,1,1,255,4,4,3,2,7,128,
   48,29,6,3,85,29,37,4,22,48,20,6,8,43,6,1,5,5,7,3,1,
   6,8,43,6,1,5,5,7,3,2]

def hostPublic (kind : Nat) (secret : List UInt8) : Except Error (List UInt8) := do
  if secret.length != 32 then throw .length
  if kind == 1 then
    Curve25519.Ed25519.publicKey secret |>.mapError (fun _ => .signing)
  else if kind == 2 then
    let key ← Weierstrass.publicKey .secp256k1 (Weierstrass.readBE secret)
      |>.mapError (fun _ => .signing)
    return Weierstrass.encodePoint true key
  else throw .key

def hostSign (kind : Nat) (secret message : List UInt8) : Except Error (List UInt8) := do
  if secret.length != 32 then throw .length
  if kind == 1 then
    Curve25519.Ed25519.sign secret message |>.mapError (fun _ => .signing)
  else if kind == 2 then
    let sig ← Weierstrass.sign .secp256k1 (Weierstrass.readBE secret) (← hash message)
      |>.mapError (fun _ => .signing)
    return Weierstrass.der sig
  else throw .key

def tbs (spki hostKey hostSig before after : List UInt8) : Except Error (List UInt8) := do
  let signed ← tlv 48 ((← tlv 4 hostKey) ++ (← tlv 4 hostSig))
  let ext ← tlv 48 (identityOid ++ [1,1,255] ++ (← tlv 4 signed))
  let extensions ← tlv 163 (← tlv 48 (ext ++ usageExtensions))
  tlv 48 ([160,3,2,1,2,2,1,1] ++ edAlgorithm ++ issuerName ++
    (← tlv 48 (before ++ after)) ++ issuerName ++ spki ++ extensions)

structure Issued where
  der : List UInt8
  ephemeralSeed : List UInt8
  peerId : List UInt8
  deriving Repr

/-- Freshness and cryptographic entropy are caller obligations, not testable
properties of a 32-byte value. The owned seed must be wiped on completion/abort. -/
def issue (kind : Nat) (hostSecret entropy : List UInt8) (notBefore notAfter : Int) :
    Except Error Issued := do
  if entropy.length != 32 || hostSecret.length != 32 then throw .length
  if notAfter < notBefore then throw .time
  let before ← Time.encode notBefore |>.mapError (fun _ => .time)
  let after ← Time.encode notAfter |>.mapError (fun _ => .time)
  let ephemeral ← Curve25519.Ed25519.publicKey entropy |>.mapError (fun _ => .signing)
  let spki ← tlv 48 (edAlgorithm ++ (← tlv 3 (0 :: ephemeral)))
  let host ← hostPublic kind hostSecret
  let encoded ← PublicKey.encode kind host |>.mapError (fun _ => .key)
  let sig ← hostSign kind hostSecret (hostPrefix ++ spki)
  let body ← tbs spki encoded sig before after
  let self ← Curve25519.Ed25519.sign entropy body |>.mapError (fun _ => .signing)
  let der ← tlv 48 (body ++ edAlgorithm ++ (← tlv 3 (0 :: self)))
  let peer ← PublicKey.peerId kind host |>.mapError (fun _ => .key)
  return ⟨der, entropy, peer⟩

end Libp2pAsm.Spec.Identity.Certificate
