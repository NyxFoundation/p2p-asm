import Libp2pAsm.Refinement.AsmCodec.QuicArithmetic

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

theorem word_shift_zero_iff (v : Word) (n : Nat) :
    (v >>> n = 0) ↔ v.toNat < 2^n := by
  constructor
  · intro h
    have he := congrArg BitVec.toNat h
    have hp : 0 < 2^n := Nat.pow_pos (by decide)
    simp [Nat.shiftRight_eq_div_pow] at he
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]

theorem word_shift_nonzero (v : Word) (n : Nat) (h : 2^n ≤ v.toNat) : v >>> n ≠ 0 := by
  intro he
  have := (word_shift_zero_iff v n).1 he
  omega

end Libp2pAsm.Refinement.AsmCodec
