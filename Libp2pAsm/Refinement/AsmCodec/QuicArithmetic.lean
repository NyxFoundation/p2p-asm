import Libp2pAsm.Rv64.Logic.Bytes
import Libp2pAsm.Refinement.Codec.QuicHelpers

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

set_option backward.isDefEq.respectTransparency false

theorem byte_word_nat (b : UInt8) : (BitVec.ofNat 64 b.toNat).toNat = b.toNat := by
  have h := b.toNat_lt
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show b.toNat < 2^64 by omega)]

theorem quic_tag_word (b : UInt8) :
    BitVec.ofNat 64 b.toNat >>> (6 : Nat) = BitVec.ofNat 64 (b.toNat / 64) := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftRight_eq_div_pow]
  have h := b.toNat_lt
  omega

theorem quic_width_bound (b : UInt8) : 1 ≤ 2^(b.toNat / 64) ∧ 2^(b.toNat / 64) ≤ 8 := by
  have hb := b.toNat_lt
  have ht : b.toNat / 64 = 0 ∨ b.toNat / 64 = 1 ∨ b.toNat / 64 = 2 ∨ b.toNat / 64 = 3 := by omega
  rcases ht with h | h | h | h <;> simp [h]

theorem quic_width_word (b : UInt8) :
    (1 : Word) <<< ((BitVec.ofNat 64 b.toNat >>> (6 : Nat)).toNat % 64) =
      BitVec.ofNat 64 (2^(b.toNat / 64)) := by
  rw [quic_tag_word]
  have hb := b.toNat_lt
  have ht : b.toNat / 64 = 0 ∨ b.toNat / 64 = 1 ∨ b.toNat / 64 = 2 ∨ b.toNat / 64 = 3 := by omega
  rcases ht with h | h | h | h <;> simp [h]

theorem quic_payload_word (b : UInt8) :
    BitVec.ofNat 64 b.toNat &&& (63 : Word) = BitVec.ofNat 64 (b.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, byte_word_nat]
  change (b.toNat &&& 63) = (b.toNat % 64) % 2^64
  have hm : b.toNat &&& 63 = b.toNat % 64 := Nat.and_two_pow_sub_one_eq_mod b.toNat 6
  rw [hm]
  omega

theorem append_byte_nat (acc : Word) (b : UInt8) :
    (acc <<< (8 : Nat) ||| BitVec.ofNat 64 b.toNat).toNat =
      (acc.toNat * 256 + b.toNat) % 2^64 := by
  rw [shift_or_byte acc _ (byte_word_bound b)]
  simp [BitVec.toNat_add, BitVec.toNat_mul, Nat.add_mod, Nat.mul_mod]

/-- Arithmetic correspondence for every tail, without enumerating byte values. -/
theorem foldBytes_nat (bytes : List UInt8) (acc : Word) :
    (foldBytes bytes acc).toNat =
      (bytes.foldl (fun a b => a * 256 + b.toNat) acc.toNat) % 2^64 := by
  induction bytes generalizing acc with
  | nil => simp [foldBytes, Nat.mod_eq_of_lt acc.isLt]
  | cons b bs ih =>
    simp only [foldBytes, List.foldl_cons] at *
    rw [ih, append_byte_nat]
    have aux (xs : List UInt8) (a : Nat) :
        (xs.foldl (fun n b => n * 256 + b.toNat) (a % 2^64)) % 2^64 =
          (xs.foldl (fun n b => n * 256 + b.toNat) a) % 2^64 := by
      induction xs generalizing a with
      | nil => simp
      | cons x xs ih =>
        simp only [List.foldl_cons]
        rw [← ih, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
        rw [← Nat.mul_mod, ← Nat.add_mod, ih]
    exact aux bs _

theorem foldBytes_ofNat (bytes : List UInt8) (acc : Nat) :
    foldBytes bytes (BitVec.ofNat 64 acc) =
      BitVec.ofNat 64 (bytes.foldl (fun a b => a * 256 + b.toNat) acc) := by
  induction bytes generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    have he : (BitVec.ofNat 64 acc <<< (8 : Nat) ||| BitVec.ofNat 64 b.toNat) =
        BitVec.ofNat 64 (acc * 256 + b.toNat) := by
      rw [shift_or_byte _ _ (byte_word_bound b)]
      simp [BitVec.ofNat_add, BitVec.ofNat_mul]
    simpa only [foldBytes, List.foldl_cons, he] using ih (acc * 256 + b.toNat)

end Libp2pAsm.Refinement.AsmCodec
