import Libp2pAsm.Refinement.Crypto.RSA.Encoding

namespace Libp2pAsm.Refinement.Crypto.RSA

theorem multiply_add_fits (a b carry slot : Nat)
    (ha : a < 2^32) (hb : b < 2^32) (hc : carry < 2^32) (hs : slot < 2^32) :
    a*b+carry+slot < 2^64 := by
  have h := Nat.mul_le_mul (show a ≤ 2^32-1 by omega) (show b ≤ 2^32-1 by omega)
  omega

theorem multiply_add_carry (a b carry slot : Nat)
    (ha : a < 2^32) (hb : b < 2^32) (hc : carry < 2^32) (hs : slot < 2^32) :
    (a*b+carry+slot)/2^32 < 2^32 := by
  have := multiply_add_fits a b carry slot ha hb hc hs
  omega

theorem limb_reconstruction (n : Nat) : n%2^32+2^32*(n/2^32) = n :=
  Nat.mod_add_div _ _

theorem double_carry (a c : Nat) (ha : a < 2^32) (hc : c ≤ 1) :
    (2*a+c)/2^32 ≤ 1 := by omega

theorem subtraction_borrow (a b c : Nat) (ha : a < 2^32)
    (hb : b < 2^32) (hc : c ≤ 1) :
    (if a < b+c then 1 else 0) ≤ (1 : Nat) ∧
    a+2^32*(if a < b+c then 1 else 0)-(b+c) < 2^32 := by
  split <;> omega

theorem subtract_once (n x : Nat) (_hn : 0 < n) (hx : x < 2*n) :
    (if x < n then x else x-n) = x%n := by
  split
  next h => exact (Nat.mod_eq_of_lt h).symm
  next h => rw [Nat.mod_eq_sub_mod (by omega : n ≤ x), Nat.mod_eq_of_lt (by omega)]

theorem montgomery_cancel (n inverse x : Nat) (h : (1+n*inverse)%2^32 = 0) :
    (x + (x*inverse)*n)%2^32 = 0 := by
  have eq : x+(x*inverse)*n = x*(1+n*inverse) := by
    simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
  rw [eq, Nat.mul_mod, h]
  simp

theorem modexp_range (a e n : Nat) (hn : 0 < n) :
    Spec.Crypto.RSA.modexp a e n < n := by
  rw [Spec.Crypto.RSA.modexp]
  split <;> exact Nat.mod_lt _ hn

end Libp2pAsm.Refinement.Crypto.RSA
