import Libp2pAsm.Refinement.Clock.Raw

namespace Libp2pAsm.Refinement.Clock

open Rv64

theorem monotonic_guard (old : RawState) (sample : RawSample) :
    (sample.toSpec.sourceStatus ≥ 2 ∨ sample.toSpec.beforeNs ≥ 2^64 ∨ sample.toSpec.afterNs ≥ 2^64 ∨
      sample.toSpec.afterNs < sample.toSpec.beforeNs ∨
      (old.toSpec.mode ≠ 0 ∧ sample.toSpec.beforeNs < old.toSpec.afterNs)) ↔ monotonicBad old sample := by
  have hb := sample.beforeNs.isLt
  have ha := sample.afterNs.isLt
  have hm : old.mode ≠ 0 ↔ old.mode.toNat ≠ 0 := by simp [← BitVec.toNat_inj]
  simp only [monotonicBad, RawSample.toSpec, RawState.toSpec, BitVec.lt_def, BitVec.le_def, hm]
  change (_ ∨ _ ∨ _ ∨ _ ∨ _) ↔ (¬sample.status.toNat < 2 ∨ _ ∨ _)
  omega

theorem wall_guard (sample : RawSample) (span : Word)
    (hst : sample.status < 2) (hnow : sample.beforeNs ≤ sample.afterNs) :
    (sample.toSpec.sourceStatus = 1 ∨ sample.toSpec.afterNs-sample.toSpec.beforeNs > span.toNat ∨
      sample.toSpec.nanos ≥ 1000000000 ∨ sample.toSpec.seconds < -(2^63) ∨ sample.toSpec.seconds ≥ 2^63) ↔
      wallBad sample span := by
  have hs : sample.status.toNat < 2 := hst
  have hlo : -(2^63 : Int) ≤ sample.seconds.toInt := BitVec.le_toInt _
  have hhi : sample.seconds.toInt < (2^63 : Int) := BitVec.toInt_lt
  have hz : sample.status ≠ 0 ↔ sample.status.toNat ≠ 0 := by simp [← BitVec.toNat_inj]
  simp only [wallBad, RawSample.toSpec, hz, BitVec.le_def, BitVec.lt_def,
    BitVec.toNat_sub_of_le hnow]
  change (_ ∨ _ ∨ _ ∨ _ ∨ _) ↔ (_ ∨ _ ∨ ¬sample.nanos.toNat < 1000000000)
  omega

theorem monotonic_good {old : RawState} {sample : RawSample} (h : ¬monotonicBad old sample) :
    sample.status < 2 ∧ sample.beforeNs ≤ sample.afterNs ∧ (old.mode ≠ 0 → old.afterNs ≤ sample.beforeNs) := by
  by_cases hs : sample.status < 2
  case neg => exact False.elim (h (Or.inl hs))
  by_cases hn : sample.beforeNs ≤ sample.afterNs
  case neg => exact False.elim (h (Or.inr (Or.inl hn)))
  refine ⟨hs, hn, ?_⟩
  intro hm
  by_cases hp : old.afterNs ≤ sample.beforeNs
  · exact hp
  · exact False.elim (h (Or.inr (Or.inr ⟨hm, hp⟩)))

theorem wall_good {sample : RawSample} {span : Word} (h : ¬wallBad sample span) :
    sample.status = 0 ∧ sample.afterNs-sample.beforeNs ≤ span ∧ sample.nanos < 1000000000 := by
  by_cases hs : sample.status = 0
  case neg => exact False.elim (h (Or.inl hs))
  by_cases hw : sample.afterNs-sample.beforeNs ≤ span
  case neg => exact False.elim (h (Or.inr (Or.inl hw)))
  by_cases hn : sample.nanos < 1000000000
  · exact ⟨hs, hw, hn⟩
  · exact False.elim (h (Or.inr (Or.inr hn)))

end Libp2pAsm.Refinement.Clock
