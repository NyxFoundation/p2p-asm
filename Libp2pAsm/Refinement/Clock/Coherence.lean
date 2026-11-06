import Libp2pAsm.Refinement.Clock.Raw

namespace Libp2pAsm.Refinement.Clock

open Rv64

theorem backwards_iff_negative (old : RawState) (sample : RawSample)
    (ho : old.nanos < 1000000000) (hn : sample.nanos < 1000000000) :
    wallBackwards old sample ↔ wallElapsed old sample < 0 := by
  have ho' : old.nanos.toNat < 1000000000 := ho
  have hn' : sample.nanos.toNat < 1000000000 := hn
  have heq : sample.seconds = old.seconds ↔ sample.seconds.toInt = old.seconds.toInt :=
    BitVec.toInt_inj.symm
  simp only [wallBackwards, wallElapsed, heq, BitVec.le_def]
  omega

theorem elapsed_exact (old : RawState) (sample : RawSample)
    (ho : old.nanos < 1000000000) (hn : sample.nanos < 1000000000)
    (hb : ¬wallBackwards old sample) :
    ((elapsedHigh (secondsPart old sample) (nanosPart old sample)).toNat*2^64+
      (elapsedLow (secondsPart old sample) (nanosPart old sample)).toNat : Nat) =
      (wallElapsed old sample).toNat := by
  have horder : old.seconds.toInt ≤ sample.seconds.toInt := by
    have h := hb; unfold wallBackwards at h; omega
  have hequal : sample.seconds = old.seconds → old.nanos ≤ sample.nanos := by
    intro heq
    by_cases hle : old.nanos ≤ sample.nanos
    · exact hle
    · exact False.elim (hb (Or.inr ⟨heq, hle⟩))
  have hp := elapsed_parts old sample ho hn horder hequal
  have hm := multiply_with_carry (secondsPart old sample) (nanosPart old sample) (nanosPart_small old sample ho hn)
  omega

theorem coherent_exact (old : RawState) (sample : RawSample) (drift : Word)
    (ho : old.nanos < 1000000000) (hn : sample.nanos < 1000000000) (hm : old.afterNs ≤ sample.afterNs) :
    coherent old sample drift ↔ 0 ≤ wallElapsed old sample ∧
      (wallElapsed old sample - (sample.afterNs.toNat-old.afterNs.toNat : Nat)).natAbs ≤ drift.toNat := by
  have hb := backwards_iff_negative old sample ho hn
  by_cases hback : wallBackwards old sample
  · have hneg := hb.mp hback
    simp only [coherent, hback, not_true_eq_false, false_and]
    constructor
    · exact False.elim
    · intro h; omega
  have hnonneg : 0 ≤ wallElapsed old sample := by
    have hn : ¬wallElapsed old sample < 0 := fun h => hback (hb.mpr h)
    omega
  have he := elapsed_exact old sample ho hn hback
  unfold coherent
  rw [withinDrift_exact, he, BitVec.toNat_sub_of_le hm]
  simp [hback, hnonneg, Int.toNat_of_nonneg hnonneg]

end Libp2pAsm.Refinement.Clock
