import Libp2pAsm.Refinement.AsmCodec.EncodeArithmetic

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

set_option backward.isDefEq.respectTransparency false

def quicByte (value shift tag : Word) : Word :=
  (value >>> (shift.toNat % 64) &&& 255) ||| tag

def quicOutput : Nat → Word → Word → Word → List UInt8
  | 0, _, _, _ => []
  | n+1, value, shift, tag =>
    (quicByte value shift tag).toNat.toUInt8 :: quicOutput n value (shift + (-8)) 0

@[simp] theorem quicOutput_length (n : Nat) (v shift tag : Word) :
    (quicOutput n v shift tag).length = n := by
  induction n generalizing shift tag <;> simp [quicOutput, *]

theorem quic_widthTag_bounds (v : Nat) :
    1 ≤ (Spec.Codec.QuicVarint.widthTag v).1 ∧ (Spec.Codec.QuicVarint.widthTag v).1 ≤ 8 := by
  unfold Spec.Codec.QuicVarint.widthTag
  split <;> (try split) <;> (try split) <;> decide

theorem quicByte_zero (v : Word) (shift : Nat) (hs : shift < 64) :
    (quicByte v (BitVec.ofNat 64 shift) 0).toNat.toUInt8 =
      (v.toNat / 2^shift % 256).toUInt8 := by
  have hs64 : shift < 2^64 := by omega
  have hm (n : Nat) : n &&& 255 = n % 256 := Nat.and_two_pow_sub_one_eq_mod n 8
  simp [quicByte, Nat.mod_eq_of_lt hs64, Nat.mod_eq_of_lt hs,
    Nat.shiftRight_eq_div_pow, hm]

theorem quicByte_header (v : Word) (shift tag : Nat) (hs : shift < 64)
    (hq : v.toNat / 2^shift < 64) (ht : tag = 0 ∨ tag = 64 ∨ tag = 128 ∨ tag = 192) :
    (quicByte v (BitVec.ofNat 64 shift) (BitVec.ofNat 64 tag)).toNat.toUInt8 =
      (tag + v.toNat / 2^shift).toUInt8 := by
  have hs64 : shift < 2^64 := by omega
  have hm (n : Nat) : n &&& 255 = n % 256 := Nat.and_two_pow_sub_one_eq_mod n 8
  have hq256 : v.toNat / 2^shift < 256 := by omega
  have hor : v.toNat / 2^shift ||| tag = tag + v.toNat / 2^shift := by
    rcases ht with rfl | rfl | rfl | rfl
    · simp
    · simpa [Nat.or_comm] using (Nat.shiftLeft_add_eq_or_of_lt (i := 6) hq 1).symm
    · simpa [Nat.or_comm] using (Nat.shiftLeft_add_eq_or_of_lt (i := 6) hq 2).symm
    · simpa [Nat.or_comm] using (Nat.shiftLeft_add_eq_or_of_lt (i := 6) hq 3).symm
  have ht256 : tag < 256 := by rcases ht with rfl | rfl | rfl | rfl <;> decide
  simp [quicByte, Nat.mod_eq_of_lt hs64, Nat.mod_eq_of_lt hs,
    Nat.shiftRight_eq_div_pow, hm, Nat.mod_eq_of_lt hq256,
    Nat.mod_eq_of_lt (show tag < 2^64 by omega), hor]

theorem quicOutput_spec (v : Word) (hv : v.toNat < 2^62) :
    Spec.Codec.QuicVarint.encode v.toNat = .ok
      (quicOutput (Spec.Codec.QuicVarint.widthTag v.toNat).1 v
        (BitVec.ofNat 64 (8 * ((Spec.Codec.QuicVarint.widthTag v.toNat).1 - 1)))
        (BitVec.ofNat 64 (Spec.Codec.QuicVarint.widthTag v.toNat).2)) := by
  have hn : ¬v.toNat ≥ 2^62 := by omega
  have hz0 := quicByte_zero v 0 (by decide)
  have hz8 := quicByte_zero v 8 (by decide)
  have hz16 := quicByte_zero v 16 (by decide)
  have hz24 := quicByte_zero v 24 (by decide)
  have hz32 := quicByte_zero v 32 (by decide)
  have hz40 := quicByte_zero v 40 (by decide)
  have hz48 := quicByte_zero v 48 (by decide)
  simp at hz0 hz8 hz16 hz24 hz32 hz40 hz48
  by_cases h6 : v.toNat < 2^6
  · have hh := quicByte_header v 0 0 (by decide) (by simpa using h6) (.inl rfl)
    simp [Spec.Codec.QuicVarint.encode, hn, Spec.Codec.QuicVarint.widthTag, h6,
      quicOutput, Spec.Codec.QuicVarint.bigEndian, hh]
  · by_cases h14 : v.toNat < 2^14
    · have hh := quicByte_header v 8 64 (by decide) (by omega) (.inr (.inl rfl))
      simp [Spec.Codec.QuicVarint.encode, hn, Spec.Codec.QuicVarint.widthTag, h6, h14,
        quicOutput, Spec.Codec.QuicVarint.bigEndian, List.range_succ, hh, hz0]
    · by_cases h30 : v.toNat < 2^30
      · have hh := quicByte_header v 24 128 (by decide) (by omega) (.inr (.inr (.inl rfl)))
        simp [Spec.Codec.QuicVarint.encode, hn, Spec.Codec.QuicVarint.widthTag, h6, h14, h30,
          quicOutput, Spec.Codec.QuicVarint.bigEndian, List.range_succ, hh, hz0, hz8, hz16]
      · have hh := quicByte_header v 56 192 (by decide) (by omega) (.inr (.inr (.inr rfl)))
        simp [Spec.Codec.QuicVarint.encode, hn, Spec.Codec.QuicVarint.widthTag, h6, h14, h30,
          quicOutput, Spec.Codec.QuicVarint.bigEndian, List.range_succ, hh,
          hz0, hz8, hz16, hz24, hz32, hz40, hz48]


end Libp2pAsm.Refinement.AsmCodec
