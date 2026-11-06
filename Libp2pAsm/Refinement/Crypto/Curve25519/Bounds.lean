import Libp2pAsm.Spec.Crypto.Curve25519.Field

/-! Universal integer arithmetic facts for the limb algorithms. These are not
instruction-level primitive refinement, resource or constant-time proofs. -/
namespace Libp2pAsm.Refinement.Crypto.Curve25519
open Spec.Crypto.Curve25519

theorem radix_split (n : Nat) : n % 2^51 + 2^51 * (n / 2^51) = n := by omega

theorem word_split (n : Nat) : n % 2^64 + 2^64 * (n / 2^64) = n := by omega

theorem high_word_bound (n : Nat) (h : n < 2^128) : n / 2^64 < 2^64 := by omega

theorem carry_preserves (a b : Nat) :
    a % 2^51 + 2^51 * (b + a / 2^51) = a + 2^51*b := by omega

theorem field_fold (lo hi : Nat) :
    (lo + 2^255*hi) % prime = (lo + 19*hi) % prime := by
  rw [Nat.add_mod lo (2^255*hi), Nat.add_mod lo (19*hi),
    Nat.mul_mod (2^255) hi, Nat.mul_mod 19 hi]
  rfl

theorem canonical_once (n modulus : Nat) (_hpos : 0 < modulus) (h : n < 2*modulus) :
    (if modulus ≤ n then n-modulus else n) = n % modulus := by
  split
  next hn =>
    rw [Nat.mod_eq_sub_mod hn, Nat.mod_eq_of_lt (by omega)]
  next hn => exact (Nat.mod_eq_of_lt (by omega)).symm

theorem product_bound (a b : Nat) (ha : a < 2^51) (hb : b < 19*2^51) :
    a*b < 19*2^102 := by
  have h₂ := Nat.mul_lt_mul_of_pos_right ha (by decide : 0 < 19*2^51)
  have h₃ := Nat.mul_le_mul_left a (Nat.le_of_lt hb)
  omega

theorem convolution_carry_bound (n : Nat) (h : n < 95*2^102 + 2^58) :
    n < 2^109 ∧ n / 2^51 < 2^58 := by omega

theorem final_fold_word_bound (lo carry : Nat) (hl : lo < 2^51) (hc : carry < 2^58) :
    lo + 19*carry < 2^63 := by omega

theorem addition_word_bound (a b : Nat) (ha : a < 2^51) (hb : b < 2^51) :
    a+b < 2^52 := by omega

theorem subtraction_word_bound (a b : Nat) (ha : a < 2^51) (hb : b < 2^51) :
    b ≤ a + 2*(2^51-19) ∧ a+2*(2^51-1)-b < 2^53 := by omega

theorem scalar_step_bound (r bit : Nat) (hr : r < order) (hb : bit ≤ 1) :
    2*r+bit < 2*order := by omega

theorem scalar_add_bound (a b : Nat) (ha : a < order) (hb : b < order) :
    a+b < 2*order := by omega

theorem clamp_bounds (bs : List UInt8) :
    2^254 ≤ clamp bs ∧ clamp bs < 2^255 ∧ clamp bs % 8 = 0 := by
  unfold clamp
  omega

theorem workspace_bound (n : Nat) (h : n < 2^64-4160) :
    n+4160 < 2^64 ∧ n+64 < 2^64 := by omega

end Libp2pAsm.Refinement.Crypto.Curve25519
