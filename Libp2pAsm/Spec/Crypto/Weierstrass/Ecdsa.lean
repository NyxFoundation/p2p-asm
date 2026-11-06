import Libp2pAsm.Spec.Crypto.Weierstrass.Encoding
import Libp2pAsm.Spec.Crypto.HMAC

namespace Libp2pAsm.Spec.Crypto.Weierstrass

inductive Error where
  | invalidScalar | invalidPoint | invalidDigest | invalidSignature | nonceRejected
  deriving BEq, DecidableEq, Repr

def publicKey (c : Curve) (d : Nat) : Except Error Affine := do
  unless validScalar c d do throw .invalidScalar
  match mul c d (some c.generator) with
  | some p => pure p
  | none => throw .invalidPoint

def ecdh (c : Curve) (d : Nat) (q : Affine) : Except Error (List UInt8) := do
  unless onCurve c q do throw .invalidPoint
  unless validScalar c d do throw .invalidScalar
  match mul c d (some q) with
  | some p => pure (writeBE p.x)
  | none => throw .invalidPoint

def hmac (k m : List UInt8) : Except Error (List UInt8) :=
  (HMAC.sha256 k m).mapError (fun _ => .invalidDigest)

structure NonceState where
  k : List UInt8
  v : List UInt8

def nonceInit (c : Curve) (d : Nat) (digest : List UInt8) : Except Error NonceState := do
  let seed := writeBE d ++ writeBE (readBE digest % c.order)
  let k := List.replicate 32 0
  let v := List.replicate 32 1
  let k ← hmac k (v ++ [0] ++ seed)
  let v ← hmac k v
  let k ← hmac k (v ++ [1] ++ seed)
  return ⟨k, ← hmac k v⟩

def nonceNext (state : NonceState) : Except Error (Nat × NonceState) := do
  let v ← hmac state.k state.v
  return (readBE v, ⟨state.k,v⟩)

/-- RFC6979 3.2.h continuation after invalid candidate OR zero r/s.
The public signer deliberately caps the attempt budget at one and returns
nonceRejected instead of retrying/reducing/reusing a failed candidate. -/
def nonceRetry (state : NonceState) : Except Error NonceState := do
  let k ← hmac state.k (state.v ++ [0])
  return ⟨k, ← hmac k state.v⟩

def signWithNonce (c : Curve) (d z k : Nat) : Except Error Signature := do
  unless validScalar c d do throw .invalidScalar
  unless validScalar c k do throw .nonceRejected
  let some p := mul c k (some c.generator) | throw .nonceRejected
  let r := p.x % c.order
  let s := inv c.order k * (z+r*d) % c.order
  unless validScalar c r && validScalar c s do throw .nonceRejected
  return ⟨r, if c == .secp256k1 then min s (c.order-s) else s⟩

def sign (c : Curve) (d : Nat) (digest : List UInt8) : Except Error Signature := do
  unless digest.length == 32 do throw .invalidDigest
  unless validScalar c d do throw .invalidScalar
  let (k,_) ← nonceNext (← nonceInit c d digest)
  signWithNonce c d (readBE digest) k

def verify (c : Curve) (lowS : Bool) (q : Affine) (digest : List UInt8)
    (sig : Signature) : Bool :=
  if !onCurve c q || digest.length != 32 || !validSignature c lowS sig then false else
  let w := inv c.order sig.s
  let p := add c (mul c (readBE digest*w % c.order) (some c.generator))
    (mul c (sig.r*w % c.order) (some q))
  match p with | none => false | some p => p.x % c.order == sig.r

end Libp2pAsm.Spec.Crypto.Weierstrass
