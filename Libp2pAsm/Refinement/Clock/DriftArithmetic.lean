import Libp2pAsm.Refinement.Clock.Memory

namespace Libp2pAsm.Refinement.Clock

open Rv64

def distanceLow (high low mono : Word) : Word :=
  if high = 0 then (if low < mono then mono-low else low-mono) else low-mono

def distanceHigh (high low mono : Word) : Word :=
  if high = 0 then 0 else high-(if low < mono then 1 else 0)

def withinDrift (high low mono drift : Word) : Prop :=
  distanceHigh high low mono = 0 ∧ distanceLow high low mono ≤ drift

instance (high low mono drift : Word) : Decidable (withinDrift high low mono drift) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem abs_nat_difference (a b : Nat) :
    ((a : Int)-(b : Int)).natAbs = if a < b then b-a else a-b := by
  by_cases h : a < b
  · have hn : 0 ≤ (b : Int)-(a : Int) := by omega
    have he := Int.natAbs_of_nonneg hn
    rw [show (a : Int)-(b : Int) = -((b : Int)-(a : Int)) by omega, Int.natAbs_neg]
    simp only [h, if_true]
    omega
  · have hn : 0 ≤ (a : Int)-(b : Int) := by omega
    have he := Int.natAbs_of_nonneg hn
    simp only [h, if_false]
    omega

/-- Borrow across the low limb is checked before the low-limb drift comparison. -/
theorem withinDrift_exact (high low mono drift : Word) :
    withinDrift high low mono drift ↔
      (((high.toNat*2^64+low.toNat : Nat) : Int)-(mono.toNat : Int)).natAbs ≤ drift.toNat := by
  have hh := high.isLt
  have hl := low.isLt
  have hm := mono.isLt
  have hd := drift.isLt
  rw [abs_nat_difference]
  by_cases hz : high = 0
  · subst high
    by_cases hlt : low < mono
    · have hle : low ≤ mono := BitVec.le_of_lt hlt
      have hlt' : low.toNat < mono.toNat := hlt
      simp [withinDrift, distanceHigh, distanceLow, hlt, hlt',
        BitVec.le_def, BitVec.toNat_sub_of_le hle]
    · have hle : mono ≤ low := BitVec.not_lt.mp hlt
      have hlt' : ¬low.toNat < mono.toNat := hlt
      simp [withinDrift, distanceHigh, distanceLow, hlt, hlt',
        BitVec.le_def, BitVec.toNat_sub_of_le hle]
  have hhn : 0 < high.toNat := by
    have : high.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq h)
    omega
  have hwide : ¬high.toNat*2^64+low.toNat < mono.toNat := by omega
  simp only [hwide, if_false]
  unfold withinDrift distanceHigh distanceLow
  rw [if_neg hz, if_neg hz]
  by_cases hlt : low < mono
  · have hlt' : low.toNat < mono.toNat := hlt
    have hhigh : (high-1).toNat = high.toNat-1 :=
      BitVec.toNat_sub_of_le (by change 1 ≤ high.toNat; omega)
    rw [if_pos hlt]
    have hh0 : high-1 = 0 ↔ high.toNat = 1 := by
      rw [← BitVec.toNat_inj, hhigh]
      change high.toNat-1 = 0 ↔ high.toNat = 1
      omega
    rw [hh0, BitVec.le_def, BitVec.toNat_sub_of_lt hlt]
    omega
  · have hle : mono ≤ low := BitVec.not_lt.mp hlt
    rw [if_neg hlt]
    simp only [BitVec.ofNat_eq_ofNat] at hz ⊢
    rw [BitVec.sub_zero]
    simp only [hz, false_and]
    have hle' : mono.toNat ≤ low.toNat := hle
    change False ↔ high.toNat*18446744073709551616+low.toNat-mono.toNat ≤ drift.toNat
    constructor
    · exact False.elim
    · intro hbad
      omega

end Libp2pAsm.Refinement.Clock
