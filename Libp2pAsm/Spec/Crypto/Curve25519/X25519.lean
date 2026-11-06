import Libp2pAsm.Spec.Crypto.Curve25519.Field

namespace Libp2pAsm.Spec.Crypto.Curve25519.X25519

private def step (u k : Nat) (s : Nat × Nat × Nat × Nat × Bool) (i : Nat) :=
  let (x₂, z₂, x₃, z₃, swap) := s
  let bit := k.testBit (254-i)
  let (x₂, z₂, x₃, z₃) := if swap != bit then (x₃,z₃,x₂,z₂) else (x₂,z₂,x₃,z₃)
  let a := add x₂ z₂
  let aa := mul a a
  let b := sub x₂ z₂
  let bb := mul b b
  let e := sub aa bb
  let da := mul (sub x₃ z₃) a
  let cb := mul (add x₃ z₃) b
  (mul aa bb, mul e (add aa (mul 121665 e)),
    mul (add da cb) (add da cb), mul u (mul (sub da cb) (sub da cb)), bit)

/-- RFC 7748 accepts noncanonical u, masks bit 255 and reduces modulo p. -/
def raw (secret u : Bytes) : Except Error Bytes := do
  if secret.length != 32 || u.length != 32 then throw .invalidLength
  let x := decodeLE u % 2^255 % prime
  let (x₂,z₂,x₃,z₃,swap) := (List.range 255).foldl (step x (clamp secret)) (1,0,x,1,false)
  let (x,z) := if swap then (x₃,z₃) else (x₂,z₂)
  return encodeLE (mul x (inverse z)) 32

def publicKey (secret : Bytes) : Except Error Bytes := raw secret (encodeLE 9 32)

/-- TLS policy: reject all-zero results before exposing a shared secret. -/
def sharedSecret (secret u : Bytes) : Except Error Bytes := do
  let result ← raw secret u
  if result.all (· == 0) then throw .zeroSharedSecret
  return result

end Libp2pAsm.Spec.Crypto.Curve25519.X25519
