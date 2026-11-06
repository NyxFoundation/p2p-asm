import Libp2pAsm.Asm.Crypto.Weierstrass.Limbs
import Libp2pAsm.Spec.Crypto.Weierstrass.Encoding

namespace Libp2pAsm.Refinement.Crypto.Weierstrass
open Rv64

theorem carry_bound (a b c : Nat) (ha : a < 2^64) (hb : b < 2^64) (hc : c ≤ 1) :
    (a+b+c) / 2^64 ≤ 1 := by omega

theorem carry_reconstruct (a b c : Nat) :
    (a+b+c)%2^64 + 2^64*((a+b+c)/2^64) = a+b+c := Nat.mod_add_div _ _

theorem wide_add_bound (a b c t : Nat)
    (ha : a < 2^64) (hb : b < 2^64) (hc : c < 2^64) (ht : t < 2^64) :
    a*b+c+t < 2^128 := by
  have h := Nat.mul_le_mul (show a ≤ 2^64-1 by omega) (show b ≤ 2^64-1 by omega)
  omega

theorem wide_split (a b : Nat) : a*b%2^64 + 2^64*(a*b/2^64) = a*b := Nat.mod_add_div _ _

theorem subtract_once (m x : Nat) (hm : 0 < m) (hx : x < 2*m) :
    (if x < m then x else x-m) = x%m := by
  split
  next h => exact (Nat.mod_eq_of_lt h).symm
  next h => rw [Nat.mod_eq_sub_mod (by omega : m ≤ x), Nat.mod_eq_of_lt (by omega)]

theorem select_zero (a b : Word) : b ^^^ ((a ^^^ b) &&& 0) = b := by simp

theorem select_ones (a b : Word) : b ^^^ ((a ^^^ b) &&& (-1 : Word)) = a := by
  ext i h
  simp only [BitVec.getElem_xor, BitVec.getElem_and]
  have : (-1 : Word)[i] = true := by decide +revert
  rw [this]
  cases a[i] <;> cases b[i] <;> decide

theorem writeBE_length (n : Nat) : (Spec.Crypto.Weierstrass.writeBE n).length = 32 := by
  simp [Spec.Crypto.Weierstrass.writeBE]

theorem compact_length (s : Spec.Crypto.Weierstrass.Signature) :
    (Spec.Crypto.Weierstrass.compact s).length = 64 := by
  simp [Spec.Crypto.Weierstrass.compact, writeBE_length]

theorem generator_on_curve (c : Spec.Crypto.Weierstrass.Curve) :
    Spec.Crypto.Weierstrass.onCurve c c.generator = true := by cases c <;> decide

theorem montgomery_inverse (c : Spec.Crypto.Weierstrass.Curve) (scalar : Bool) :
    let m := if scalar then c.order else c.prime
    (m * Asm.Crypto.Weierstrass.negInverse m + 1) % 2^64 = 0 := by
  cases c <;> cases scalar <;> decide

end Libp2pAsm.Refinement.Crypto.Weierstrass
