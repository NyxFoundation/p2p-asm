import Libp2pAsm.Refinement.Clock.Coherence
import Libp2pAsm.Refinement.Clock.SpecGuards

namespace Libp2pAsm.Refinement.Clock

open Rv64

theorem invalid_raw (old : RawState) (h : ¬validRaw old) :
    ¬old.mode ≤ 4 ∨ ((old.mode = 1 ∨ old.mode = 4) ∧ ¬old.nanos < 1000000000) := by
  by_cases hm : old.mode ≤ 4
  case neg => exact Or.inl hm
  by_cases hn : old.nanos < 1000000000
  · exact False.elim (h ⟨hm, fun _ => hn⟩)
  by_cases hw : old.mode = 1 ∨ old.mode = 4
  · exact Or.inr ⟨hw, hn⟩
  · exact False.elim (h ⟨hm, fun hh => False.elim (hw hh)⟩)

theorem running_nanos (old : RawState) (hv : validRaw old)
    (hm0 : old.mode ≠ 0) (hm2 : old.mode ≠ 2) (hm3 : old.mode ≠ 3) : old.nanos < 1000000000 := by
  apply hv.2
  have hm : old.mode.toNat ≤ 4 := hv.1
  have h0 : old.mode.toNat ≠ 0 := fun h => hm0 (BitVec.eq_of_toNat_eq h)
  have h2 : old.mode.toNat ≠ 2 := fun h => hm2 (BitVec.eq_of_toNat_eq h)
  have h3 : old.mode.toNat ≠ 3 := fun h => hm3 (BitVec.eq_of_toNat_eq h)
  have hh : old.mode.toNat = 1 ∨ old.mode.toNat = 4 := by omega
  rcases hh with h | h
  · exact Or.inl (BitVec.eq_of_toNat_eq h)
  · exact Or.inr (BitVec.eq_of_toNat_eq h)

theorem raw_refines_spec (old : RawState) (sample : RawSample) (drift span : Word) :
    Spec.Clock.update old.toSpec sample.toSpec drift.toNat span.toNat =
      ((rawUpdate old sample drift span).1, (rawUpdate old sample drift span).2.toSpec) := by
  by_cases hlim : drift = 0 ∨ span = 0 ∨ drift < span
  · simpa only [rawUpdate, if_pos hlim] using invalid_limits_spec old.toSpec sample.toSpec drift span hlim
  have hd : drift ≠ 0 := fun h => hlim (Or.inl h)
  have hs : span ≠ 0 := fun h => hlim (Or.inr (Or.inl h))
  have hle : span ≤ drift := BitVec.not_lt.mp (fun h => hlim (Or.inr (Or.inr h)))
  by_cases hvalid : validRaw old
  case neg =>
    simpa only [rawUpdate, if_neg hlim, if_pos hvalid] using invalid_state_spec old sample.toSpec drift span hd hs hle (invalid_raw old hvalid)
  have hv : old.toSpec.valid = true := by rw [raw_state_valid]; exact decide_eq_true hvalid
  have hm3 : old.toSpec.mode = 3 ↔ old.mode = 3 := by simp [RawState.toSpec, ← BitVec.toNat_inj]
  have hm2 : old.toSpec.mode = 2 ↔ old.mode = 2 := by simp [RawState.toSpec, ← BitVec.toNat_inj]
  have hm0 : old.toSpec.mode = 0 ↔ old.mode = 0 := by simp [RawState.toSpec, ← BitVec.toNat_inj]
  simp only [Spec.Clock.update, good_limits drift span hd hs hle, if_false, hv, Bool.not_true,
    Bool.false_eq_true, hm3, monotonic_guard, rawUpdate, hlim, hvalid, not_true_eq_false]
  by_cases hmode3 : old.mode = 3
  · simp [hmode3]
  simp only [hmode3, if_false]
  by_cases hmono : monotonicBad old sample
  · simp [hmono, RawState.toSpec]
  have hg := monotonic_good hmono
  simp only [wall_guard sample span hg.1 hg.2.1]
  simp only [hmono, if_false, hm2, hm0]
  by_cases hwall : wallBad sample span
  · simp [hwall, RawState.toSpec, RawSample.toSpec]
  simp only [hwall, if_false]
  have hwg := wall_good hwall
  unfold_internal Libp2pAsm.Spec.Clock.anchor
  by_cases hmode2 : old.mode = 2
  · simp [hmode2, anchor, RawState.toSpec, RawSample.toSpec]
  simp only [hmode2, if_false]
  by_cases hmode0 : old.mode = 0
  · simp [hmode0, anchor, RawState.toSpec, RawSample.toSpec]
  have hcanonical := running_nanos old hvalid hmode0 hmode2 hmode3
  have hafter : old.afterNs ≤ sample.afterNs := BitVec.le_trans (hg.2.2 hmode0) hg.2.1
  have hc := coherent_exact old sample drift hcanonical hwg.2.2 hafter
  unfold_internal Libp2pAsm.Spec.Clock.consistent
  simp [anchor, RawState.toSpec, RawSample.toSpec, wallElapsed] at hc ⊢
  simp only [BitVec.ofNat_eq_ofNat] at hmode0 ⊢
  by_cases ht : coherent old sample drift <;> simp [← hc, hmode0, ht]

end Libp2pAsm.Refinement.Clock
