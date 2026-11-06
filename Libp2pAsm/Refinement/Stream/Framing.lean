import Libp2pAsm.Spec.Multistream.Negotiation

namespace Libp2pAsm.Refinement.Stream

/-- A canonical 7-bit group advances the accumulator without crossing the next
power-of-two boundary. Applies to each actually consumed multistream prefix byte. -/
theorem varint_accumulator_bound (acc payload shift : Nat)
    (ha : acc < 2^shift) (hb : payload < 128) :
    acc + payload * 2^shift < 2^(shift+7) := by
  calc
    acc + payload * 2^shift < 2^shift + payload * 2^shift := Nat.add_lt_add_right ha _
    _ = (payload+1) * 2^shift := by simp [Nat.add_mul, Nat.add_comm]
    _ ≤ 128 * 2^shift := Nat.mul_le_mul_right _ (by omega)
    _ = 2^(shift+7) := by simp [Nat.pow_add, Nat.mul_comm]

theorem varint_ninth_group_bound (acc payload : Nat)
    (ha : acc < 2^56) (hb : payload < 128) :
    acc + payload * 2^56 ≤ 2^63-1 := by
  have h := varint_accumulator_bound acc payload 56 ha hb
  omega

/-- Newline is counted inside the payload, not in the varint prefix. -/
theorem framed_length (lengthBytes payload : List UInt8) :
    (lengthBytes ++ payload ++ [10]).length = lengthBytes.length + payload.length + 1 := by simp [Nat.add_assoc]

end Libp2pAsm.Refinement.Stream
