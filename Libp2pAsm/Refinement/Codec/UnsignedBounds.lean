import Libp2pAsm.Refinement.Codec.UnsignedHelpers

namespace Libp2pAsm.Refinement.Codec.UnsignedVarint

open Spec.Codec Spec.Codec.UnsignedVarint

theorem payload_bound (acc shift payload : Nat) (ha : acc < 2^shift) (hp : payload < 128) :
    acc + payload * 2^shift < 2^(shift + 7) := by
  have hs : 0 < 2^shift := Nat.two_pow_pos shift
  have hm := Nat.mul_le_mul_right (2^shift) (show payload ≤ 127 by omega)
  simp only [Nat.pow_add, Nat.reducePow]
  omega

theorem decodeLoop_consumption (fuel : Nat) (input : List UInt8) (acc shift consumed : Nat)
    (d : Decoded) (hd : decodeLoop fuel input acc shift consumed = .ok d) :
    consumed < d.consumed ∧ d.consumed ≤ consumed + fuel ∧
      d.consumed ≤ consumed + input.length := by
  induction fuel generalizing input acc shift consumed with
  | zero => simp [decodeLoop] at hd
  | succ fuel ih =>
    cases input with
    | nil => simp [decodeLoop] at hd
    | cons byte rest =>
      simp only [decodeLoop] at hd
      split at hd
      · split at hd
        · cases hd
        · cases hd; simp
      · have hi := ih rest _ _ _ hd
        simp only [List.length_cons]
        omega

theorem decodeLoop_value_bound (fuel : Nat) (input : List UInt8) (acc shift consumed : Nat)
    (d : Decoded) (ha : acc < 2^shift) (hd : decodeLoop fuel input acc shift consumed = .ok d) :
    d.value < 2^(shift + 7 * fuel) := by
  induction fuel generalizing input acc shift consumed with
  | zero => simp [decodeLoop] at hd
  | succ fuel ih =>
    cases input with
    | nil => simp [decodeLoop] at hd
    | cons byte rest =>
      have hs := payload_bound acc shift (byte.toNat % 128) ha (by omega)
      simp only [decodeLoop] at hd
      split at hd
      · split at hd
        · cases hd
        · cases hd
          exact Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (by decide) (by omega))
      · have hi := ih rest _ _ _ hs hd
        simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm 7] using hi

end Libp2pAsm.Refinement.Codec.UnsignedVarint
