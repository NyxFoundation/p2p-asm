import Libp2pAsm.Refinement.AsmCodec.QuicArithmetic

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

set_option backward.isDefEq.respectTransparency false

theorem unsigned_payload_word (b : UInt8) :
    BitVec.ofNat 64 b.toNat &&& (127 : Word) = BitVec.ofNat 64 (b.toNat % 128) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, byte_word_nat]
  change (b.toNat &&& 127) = (b.toNat % 128) % 2^64
  rw [show b.toNat &&& 127 = b.toNat % 128 from Nat.and_two_pow_sub_one_eq_mod b.toNat 7]
  omega

theorem unsigned_flag_word (b : UInt8) :
    BitVec.ofNat 64 b.toNat >>> (7 : Nat) =
      if b.toNat < 128 then (0 : Word) else 1 := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.toNat_lt
  simp [Nat.shiftRight_eq_div_pow]
  split <;> simp_all <;> omega

theorem word_shift_ofNat (n shift : Nat) :
    BitVec.ofNat 64 n <<< shift = BitVec.ofNat 64 (n <<< shift) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_mod]

theorem unsigned_accumulate (acc count : Nat) (b : UInt8) (hc : count < 9)
    (ha : acc < 2^(7*count)) :
    (BitVec.ofNat 64 acc ||| ((BitVec.ofNat 64 b.toNat &&& (127 : Word)) <<<
      ((BitVec.ofNat 64 (7*count)).toNat % 64))) =
        BitVec.ofNat 64 (acc + b.toNat % 128 * 2^(7*count)) := by
  have hs : 7 * count < 64 := by omega
  have hs64 : 7 * count < 2^64 := by omega
  rw [unsigned_payload_word]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs64, Nat.mod_eq_of_lt hs]
  rw [word_shift_ofNat, ← BitVec.ofNat_or, Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.add_comm]

theorem unsigned_accumulate_bound (acc count : Nat) (b : UInt8)
    (ha : acc < 2^(7*count)) :
    acc + b.toNat % 128 * 2^(7*count) < 2^(7*(count+1)) := by
  have hb : b.toNat % 128 < 128 := Nat.mod_lt _ (by decide)
  rw [Nat.mul_add, Nat.pow_add]
  have hp : 0 < 2^(7*count) := Nat.pow_pos (by decide)
  have hm := Nat.mul_le_mul_right (2^(7*count)) (show b.toNat % 128 ≤ 127 by omega)
  simp only [Nat.mul_one, Nat.reducePow]
  omega

end Libp2pAsm.Refinement.AsmCodec
