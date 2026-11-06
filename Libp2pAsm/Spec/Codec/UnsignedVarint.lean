import Libp2pAsm.Spec.Codec.Basic

namespace Libp2pAsm.Spec.Codec.UnsignedVarint

def encodeLoop : Nat → Nat → Except Error (List UInt8)
  | 0, _ => .error .overflow
  | remaining + 1, value => do
    if value < 128 then return [value.toUInt8]
    let tail ← encodeLoop remaining (value / 128)
    return (value % 128 + 128).toUInt8 :: tail

/-- Multiformats limits unsigned LEB128 to nine bytes and requires minimal encoding. -/
def encode (value : Nat) : Except Error (List UInt8) :=
  if value ≥ 2^63 then .error .overflow else encodeLoop 9 value

def decodeLoop : Nat → List UInt8 → Nat → Nat → Nat → Except Error Decoded
  | 0, _, _, _, _ => .error .overflow
  | _ + 1, [], _, _, _ => .error .truncated
  | remaining + 1, byte :: rest, acc, shift, consumed =>
    let payload := byte.toNat % 128
    let value := acc + payload * 2^shift
    if byte.toNat < 128 then
      if consumed > 0 && payload == 0 then .error .nonMinimal
      else .ok ⟨value, consumed + 1⟩
    else decodeLoop remaining rest value (shift + 7) (consumed + 1)

def decode (input : List UInt8) : Except Error Decoded :=
  decodeLoop 9 input 0 0 0

theorem encode_overflow (value : Nat) (h : 2^63 ≤ value) :
    encode value = .error .overflow := by
  simp [encode, h]

theorem decode_empty : decode [] = .error .truncated := rfl

end Libp2pAsm.Spec.Codec.UnsignedVarint
