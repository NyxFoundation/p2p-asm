import Libp2pAsm.Refinement.Codec.UnsignedBounds
import Libp2pAsm.Refinement.Codec.UnsignedWidth

namespace Libp2pAsm.Refinement.Codec.UnsignedVarint

open Spec.Codec Spec.Codec.UnsignedVarint

theorem pow_seven (n : Nat) : 2^(7 * n) = 128^n := by
  rw [Nat.pow_mul]

theorem decodeLoop_width_bounds (fuel : Nat) (input : List UInt8) (acc shift consumed : Nat)
    (d : Decoded) (hs : shift = 7 * consumed) (ha : acc < 2^shift)
    (hd : decodeLoop fuel input acc shift consumed = .ok d) :
    d.value < 128^d.consumed ∧ (d.consumed = 1 ∨ 128^(d.consumed - 1) ≤ d.value) := by
  induction fuel generalizing input acc shift consumed with
  | zero => simp [decodeLoop] at hd
  | succ fuel ih =>
    cases input with
    | nil => simp [decodeLoop] at hd
    | cons byte rest =>
      have hv := payload_bound acc shift (byte.toNat % 128) ha (by omega)
      simp only [decodeLoop] at hd
      split at hd
      · split at hd
        · cases hd
        · rename_i hm
          cases hd
          constructor
          · simpa [← pow_seven, hs, Nat.mul_add] using hv
          · by_cases hc : consumed = 0
            · exact Or.inl (by simp [hc])
            · right
              have hp : 1 ≤ byte.toNat % 128 := by simp at hm; omega
              have hl := Nat.mul_le_mul_right (2^shift) hp
              simp only [Nat.one_mul] at hl
              simp only [Nat.add_sub_cancel, ← pow_seven, ← hs]
              omega
      · exact ih rest _ _ _ (by omega) hv hd

/-- Every successful decode has precisely the unique minimal unsigned-varint width. -/
theorem decode_width (input : List UInt8) (d : Decoded) (hd : decode input = .ok d) :
    d.value < 128^d.consumed ∧ (d.consumed = 1 ∨ 128^(d.consumed - 1) ≤ d.value) :=
  decodeLoop_width_bounds 9 input 0 0 0 d rfl (by decide) hd

end Libp2pAsm.Refinement.Codec.UnsignedVarint
