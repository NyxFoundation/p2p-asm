import Libp2pAsm.Spec.Codec.QuicVarint

namespace Libp2pAsm.Refinement.Codec.QuicVarint

open Spec.Codec Spec.Codec.QuicVarint

@[simp] theorem bigEndian_length (count value : Nat) :
    (bigEndian count value).length = count := by
  simp [bigEndian]

theorem header_nat (payload tag : Nat) (hp : payload < 64) (ht : tag < 4) :
    ((64 * tag + payload).toUInt8.toNat / 64 = tag) ∧
      ((64 * tag + payload).toUInt8.toNat % 64 = payload) := by
  simp only [Nat.toUInt8, UInt8.toNat_ofNat']
  omega

/-- Any legal QUIC width accepts every fitting value, including non-minimal representations. -/
theorem decode_fixedWidth (tag value : Nat) (suffix : List UInt8) (ht : tag < 4)
    (hv : value < 64 * 256^(2^tag - 1)) :
    decode (((64 * tag + value / 256^(2^tag - 1)).toUInt8 ::
      bigEndian (2^tag - 1) value) ++ suffix) = .ok ⟨value, 2^tag⟩ := by
  have hp : value / 256^(2^tag - 1) < 64 := by
    apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).2
    exact hv
  have hh := header_nat (value / 256^(2^tag - 1)) tag hp ht
  have hc : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  all_goals
    simp only [Nat.toUInt8, UInt8.toNat_ofNat', Nat.reducePow, Nat.reduceSub,
      Nat.reduceMul, Nat.div_one, Nat.zero_add,
      Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 256)] at hh
    simp [decode_cons, bigEndian, List.range_succ, hh.1, hh.2,
      Nat.toUInt8, UInt8.toNat_ofNat', Nat.add_assoc]
  all_goals
    try split
    all_goals try simp only [Except.ok.injEq, Decoded.mk.injEq, and_true]
    all_goals omega

theorem fold_value_bound (bytes : List UInt8) (acc bound : Nat) (ha : acc < bound) :
    bytes.foldl (fun n byte => n * 256 + byte.toNat) acc < bound * 256^bytes.length := by
  induction bytes generalizing acc bound with
  | nil => simpa using ha
  | cons byte tail ih =>
    have hb := byte.toNat_lt
    have hs : acc * 256 + byte.toNat < bound * 256 := by omega
    have hi := ih (acc * 256 + byte.toNat) (bound * 256) hs
    simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hi

end Libp2pAsm.Refinement.Codec.QuicVarint
