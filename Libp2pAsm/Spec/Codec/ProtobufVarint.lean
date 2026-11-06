import Libp2pAsm.Spec.Codec.Basic

/-! Protobuf uint64 varints, distinct from canonical 63-bit multiformats varints.
Non-minimal encodings are accepted; the tenth byte must be zero or one. -/
namespace Libp2pAsm.Spec.Codec.ProtobufVarint
open Spec.Codec

def decodeLoop : Nat → Nat → Nat → List UInt8 → Except Error Decoded
  | 0, _, _, _ => .error .overflow
  | _+1, _, _, [] => .error .truncated
  | fuel+1, index, value, b :: rest =>
    if index == 9 && b.toNat > 1 then .error .overflow
    else
      let result := value + (b.toNat % 128) * 2^(7*index)
      if b.toNat < 128 then .ok ⟨result, index+1⟩
      else decodeLoop fuel (index+1) result rest

def decode (bytes : List UInt8) : Except Error Decoded := decodeLoop 10 0 0 bytes

end Libp2pAsm.Spec.Codec.ProtobufVarint
