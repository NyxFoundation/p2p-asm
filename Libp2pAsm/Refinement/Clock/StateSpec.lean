import Libp2pAsm.Refinement.Clock.Early

namespace Libp2pAsm.Refinement.Clock

open Rv64

theorem raw_state_valid (old : RawState) :
    old.toSpec.valid = decide (old.mode ≤ 4 ∧
      ((old.mode = 1 ∨ old.mode = 4) → old.nanos < 1000000000)) := by
  have ha := old.afterNs.isLt
  have hn := old.nanos.isLt
  have hlo : -(2^63 : Int) ≤ old.seconds.toInt := BitVec.le_toInt _
  have hhi : old.seconds.toInt < (2^63 : Int) := BitVec.toInt_lt
  have hm1 : old.mode = 1 ↔ old.mode.toNat = 1 := by simp [← BitVec.toNat_inj]
  have hm4 : old.mode = 4 ↔ old.mode.toNat = 4 := by simp [← BitVec.toNat_inj]
  change -9223372036854775808 ≤ old.seconds.toInt at hlo
  change old.seconds.toInt < 9223372036854775808 at hhi
  simp only [BitVec.ofNat_eq_ofNat] at hm1 hm4
  simp [Spec.Clock.State.valid, RawState.toSpec, ha, hn, hlo, hhi, hm1, hm4,
    BitVec.le_def, BitVec.lt_def]

theorem invalid_limits_spec (old : Spec.Clock.State) (sample : Spec.Clock.Sample) (drift span : Word)
    (hbad : drift = 0 ∨ span = 0 ∨ drift < span) :
    Spec.Clock.update old sample drift.toNat span.toNat = (.invalidLimits, old) := by
  have hb : drift.toNat = 0 ∨ drift.toNat ≥ 2^64 ∨ span.toNat = 0 ∨ span.toNat > drift.toNat := by
    rcases hbad with h | h | h
    · simp [h]
    · simp [h]
    · exact Or.inr (Or.inr (Or.inr h))
  simp [Spec.Clock.update, hb]

theorem good_limits (drift span : Word) (hd : drift ≠ 0) (hs : span ≠ 0) (hle : span ≤ drift) :
    ¬(drift.toNat = 0 ∨ drift.toNat ≥ 2^64 ∨ span.toNat = 0 ∨ span.toNat > drift.toNat) := by
  have hd' : drift.toNat ≠ 0 := fun h => hd (BitVec.eq_of_toNat_eq h)
  have hs' : span.toNat ≠ 0 := fun h => hs (BitVec.eq_of_toNat_eq h)
  have := drift.isLt
  have : span.toNat ≤ drift.toNat := hle
  omega

theorem invalid_state_spec (old : RawState) (sample : Spec.Clock.Sample) (drift span : Word)
    (hd : drift ≠ 0) (hs : span ≠ 0) (hle : span ≤ drift)
    (hbad : ¬old.mode ≤ 4 ∨ ((old.mode = 1 ∨ old.mode = 4) ∧ ¬old.nanos < 1000000000)) :
    Spec.Clock.update old.toSpec sample drift.toNat span.toNat = (.invalidState, old.toSpec) := by
  have hv : old.toSpec.valid = false := by
    rw [raw_state_valid]
    simp only [decide_eq_false_iff_not]
    intro ⟨hm, hn⟩
    rcases hbad with h | ⟨h, hns⟩
    · exact h hm
    · exact hns (hn h)
  simp [Spec.Clock.update, good_limits drift span hd hs hle, hv]

theorem stopped_spec (old : RawState) (sample : Spec.Clock.Sample) (drift span : Word)
    (hd : drift ≠ 0) (hs : span ≠ 0) (hle : span ≤ drift) (hm : old.mode = 3) :
    Spec.Clock.update old.toSpec sample drift.toNat span.toNat = (.monotonicFailure, old.toSpec) := by
  have hv : old.toSpec.valid = true := by rw [raw_state_valid]; simp [hm]
  have hmode : old.toSpec.mode = 3 := by simp [RawState.toSpec, hm]
  simp [Spec.Clock.update, good_limits drift span hd hs hle, hv, hmode]

end Libp2pAsm.Refinement.Clock
