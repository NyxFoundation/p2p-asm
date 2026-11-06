import Libp2pAsm.Refinement.Codec.UnsignedHelpers

namespace Libp2pAsm.Refinement.Codec.UnsignedVarint

open Spec.Codec Spec.Codec.UnsignedVarint

theorem encodeLoop_width (fuel value : Nat) (bytes : List UInt8)
    (he : encodeLoop fuel value = .ok bytes) :
    0 < bytes.length ∧ bytes.length ≤ fuel ∧ value < 128^bytes.length ∧
      (bytes.length = 1 ∨ 128^(bytes.length - 1) ≤ value) := by
  induction fuel generalizing value bytes with
  | zero => simp [encodeLoop] at he
  | succ fuel ih =>
    by_cases ht : value < 128
    · simp only [encodeLoop_step, ht, ↓reduceIte, Except.ok.injEq] at he
      subst bytes
      simp [ht]
    · cases hr : encodeLoop fuel (value / 128) with
      | error e => simp only [encodeLoop_step, ht, ↓reduceIte, hr] at he; cases he
      | ok tail =>
        simp only [encodeLoop_step, ht, ↓reduceIte, hr, Except.ok.injEq] at he
        subst bytes
        obtain ⟨hp, hl, hu, hm⟩ := ih _ _ hr
        simp only [List.length_cons, Nat.add_sub_cancel]
        refine ⟨by omega, by omega, ?_, Or.inr ?_⟩
        · rw [Nat.pow_succ]
          exact (Nat.div_lt_iff_lt_mul (by decide)).1 hu
        · have hq : 128^(tail.length - 1) ≤ value / 128 := by
            rcases hm with hm | hm
            · simp only [hm, Nat.sub_self, Nat.pow_zero]; omega
            · exact hm
          have hm := Nat.mul_le_mul_right 128 hq
          have hv := Nat.div_mul_le_self value 128
          have heq : 128^(tail.length - 1) * 128 = 128^tail.length := by
            rw [← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
          rw [heq] at hm
          omega

theorem minimal_width_unique (value left right : Nat) (hl : 0 < left) (hr : 0 < right)
    (hlu : value < 128^left) (hru : value < 128^right)
    (hll : left = 1 ∨ 128^(left - 1) ≤ value)
    (hrl : right = 1 ∨ 128^(right - 1) ≤ value) : left = right := by
  apply Nat.le_antisymm
  · by_cases hn : left ≤ right
    · exact hn
    have hc : right ≤ left - 1 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 128) hc
    rcases hll with hll | hll <;> omega
  · by_cases hn : right ≤ left
    · exact hn
    have hc : left ≤ right - 1 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 128) hc
    rcases hrl with hrl | hrl <;> omega

end Libp2pAsm.Refinement.Codec.UnsignedVarint
