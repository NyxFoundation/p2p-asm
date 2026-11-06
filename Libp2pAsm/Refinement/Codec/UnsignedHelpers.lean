import Libp2pAsm.Spec.Codec.UnsignedVarint

namespace Libp2pAsm.Refinement.Codec.UnsignedVarint

open Spec.Codec Spec.Codec.UnsignedVarint

@[simp] theorem terminal_byte (value : Nat) (h : value < 128) :
    value.toUInt8.toNat = value := by
  simp only [Nat.toUInt8, UInt8.toNat_ofNat']
  omega

@[simp] theorem continuation_byte (value : Nat) :
    (value % 128 + 128).toUInt8.toNat = value % 128 + 128 := by
  simp only [Nat.toUInt8, UInt8.toNat_ofNat']
  omega

theorem accumulate (value acc shift : Nat) :
    acc + value % 128 * 2^shift + (value / 128) * 2^(shift + 7) =
      acc + value * 2^shift := by
  rw [Nat.pow_add]
  have hv := Nat.mod_add_div value 128
  calc
    _ = acc + (value % 128 + 128 * (value / 128)) * 2^shift := by
      simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]
    _ = _ := by rw [hv]

theorem encodeLoop_step (fuel value : Nat) :
    encodeLoop (fuel + 1) value =
      if value < 128 then .ok [value.toUInt8]
      else match encodeLoop fuel (value / 128) with
        | .error e => .error e
        | .ok tail => .ok ((value % 128 + 128).toUInt8 :: tail) := by
  rw [encodeLoop]
  split
  · rfl
  · cases encodeLoop fuel (value / 128) <;> rfl

theorem encodeLoop_exists (fuel value : Nat) (hf : 0 < fuel)
    (hv : value < 128^fuel) :
    ∃ bytes, encodeLoop fuel value = .ok bytes ∧
      0 < bytes.length ∧ bytes.length ≤ fuel := by
  induction fuel generalizing value with
  | zero => omega
  | succ fuel ih =>
    by_cases ht : value < 128
    · exact ⟨[value.toUInt8], by simp only [encodeLoop_step, ht, ↓reduceIte], by simp, by simp⟩
    · have hf' : 0 < fuel := by
        cases fuel <;> simp_all
      have hv' : value / 128 < 128^fuel := by
        apply (Nat.div_lt_iff_lt_mul (by decide)).2
        simpa [Nat.pow_succ] using hv
      obtain ⟨bytes, he, hp, hl⟩ := ih (value / 128) hf' hv'
      refine ⟨(value % 128 + 128).toUInt8 :: bytes, ?_, by simp, ?_⟩
      · simp only [encodeLoop_step, ht, ↓reduceIte, he]
      · simp only [List.length_cons]; omega

theorem decodeLoop_encodeLoop (fuel value : Nat) (bytes suffix : List UInt8)
    (he : encodeLoop fuel value = .ok bytes) (acc shift consumed : Nat)
    (hn : consumed = 0 ∨ 0 < value) :
    decodeLoop fuel (bytes ++ suffix) acc shift consumed =
      .ok ⟨acc + value * 2^shift, consumed + bytes.length⟩ := by
  induction fuel generalizing value bytes acc shift consumed with
  | zero => simp [encodeLoop] at he
  | succ fuel ih =>
    by_cases ht : value < 128
    · simp only [encodeLoop_step, ht, ↓reduceIte, Except.ok.injEq] at he
      subst bytes
      have hm : ¬(0 < consumed ∧ value = 0) := by omega
      simp [decodeLoop, terminal_byte _ ht, Nat.mod_eq_of_lt ht, ht, hm]
    · cases hr : encodeLoop fuel (value / 128) with
      | error e => simp only [encodeLoop_step, ht, ↓reduceIte, hr] at he; cases he
      | ok tail =>
        simp only [encodeLoop_step, ht, ↓reduceIte, hr, Except.ok.injEq] at he
        subst bytes
        have hp : 0 < value / 128 := by omega
        have hi := ih (value / 128) tail hr (acc + value % 128 * 2^shift)
          (shift + 7) (consumed + 1) (Or.inr hp)
        have hc : ¬value % 128 + 128 < 128 := by omega
        have hm : (value % 128 + 128) % 128 = value % 128 := by omega
        rw [accumulate] at hi
        simp only [List.cons_append, decodeLoop, continuation_byte, hc, hm, ↓reduceIte]
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hi

end Libp2pAsm.Refinement.Codec.UnsignedVarint
