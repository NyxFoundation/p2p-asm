import Libp2pAsm.Refinement.AsmCodec.EncodeArithmetic
import Libp2pAsm.Refinement.Codec.UnsignedHelpers

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

set_option backward.isDefEq.respectTransparency false

def unsignedByte (v : Word) : Word :=
  if v >>> (7 : Nat) = 0 then v &&& 127 else (v &&& 127) ||| 128

def unsignedOutput : Nat → Word → List UInt8
  | 0, _ => []
  | n+1, v => (unsignedByte v).toNat.toUInt8 :: unsignedOutput n (v >>> (7 : Nat))

@[simp] theorem unsignedOutput_length (n : Nat) (v : Word) : (unsignedOutput n v).length = n := by
  induction n generalizing v <;> simp [unsignedOutput, *]

theorem unsignedByte_nat (v : Word) :
    (unsignedByte v).toNat.toUInt8 =
      if v.toNat < 128 then v.toNat.toUInt8 else (v.toNat % 128 + 128).toUInt8 := by
  have hm : v.toNat &&& 127 = v.toNat % 128 := Nat.and_two_pow_sub_one_eq_mod _ 7
  have hor : v.toNat % 128 ||| 128 = v.toNat % 128 + 128 := by
    simpa [Nat.or_comm, Nat.add_comm] using
      (Nat.shiftLeft_add_eq_or_of_lt (i := 7) (Nat.mod_lt v.toNat (by decide)) 1).symm
  by_cases hv : v.toNat < 128
  · have hz := (word_shift_zero_iff v 7).2 hv
    simp [unsignedByte, hv, hz, hm, Nat.mod_eq_of_lt hv]
  · have hn := word_shift_nonzero v 7 (by omega)
    simp at hn
    simp [unsignedByte, hv, hn, hm, hor]

theorem unsignedOutput_spec (fuel : Nat) (v : Word) (bytes : List UInt8)
    (he : Spec.Codec.UnsignedVarint.encodeLoop fuel v.toNat = .ok bytes) :
    unsignedOutput bytes.length v = bytes := by
  induction fuel generalizing v bytes with
  | zero => simp [Spec.Codec.UnsignedVarint.encodeLoop] at he
  | succ fuel ih =>
    by_cases hv : v.toNat < 128
    · simp only [Codec.UnsignedVarint.encodeLoop_step, hv, ↓reduceIte, Except.ok.injEq] at he
      subst bytes
      simp [unsignedOutput, unsignedByte_nat, hv]
    · cases ht : Spec.Codec.UnsignedVarint.encodeLoop fuel (v.toNat / 128) with
      | error e => simp [Codec.UnsignedVarint.encodeLoop_step, hv, ht] at he
      | ok tail =>
        simp only [Codec.UnsignedVarint.encodeLoop_step, hv, ↓reduceIte, ht, Except.ok.injEq] at he
        subst bytes
        have hs : (v >>> (7 : Nat)).toNat = v.toNat / 128 := by simp [Nat.shiftRight_eq_div_pow]
        have hi := ih (v >>> (7 : Nat)) tail (by simpa [hs] using ht)
        simpa [unsignedOutput, unsignedByte_nat, hv] using congrArg (List.cons ((v.toNat % 128 + 128).toUInt8)) hi

end Libp2pAsm.Refinement.AsmCodec
