import Libp2pAsm.Refinement.Clock.SampleTrace
import Libp2pAsm.Refinement.Clock.Specification

namespace Libp2pAsm.Refinement.Clock

open Rv64 Rv64.Logic AsmCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem raw_status_after_checks (old : RawState) (sample : RawSample) (drift span : Word)
    (hl : ¬(drift = 0 ∨ span = 0 ∨ drift < span)) (hv : validRaw old) (hm : old.mode ≠ 3) :
    BitVec.ofNat 64 (rawUpdate old sample drift span).1.code = sampleStatus old sample drift span := by
  unfold rawUpdate sampleStatus checkedStatus
  simp only [if_neg hl, if_neg (not_not_intro hv), if_neg hm]
  by_cases hmono : monotonicBad old sample
  · simp only [if_pos hmono]; rfl
  simp only [if_neg hmono]
  by_cases hwall : wallBad sample span
  · simp only [if_pos hwall]; rfl
  simp only [if_neg hwall]
  by_cases hm2 : old.mode = 2
  · simp only [if_pos hm2]; rfl
  simp only [if_neg hm2]
  by_cases hc : old.mode = 0 ∨ coherent old sample drift
  · simp only [if_pos hc]; rfl
  · simp only [if_neg hc]; rfl

theorem raw_trace (s : State) (old : RawState) (sample : RawSample) (base ptr drift span : Word)
    (bytes : Array UInt8) (frame : List Region) (hra : s.getReg .x1 = 0)
    (hbase : s.getReg .x10 = base) (hptr : s.getReg .x11 = ptr)
    (hd : s.getReg .x12 = drift) (hspan : s.getReg .x13 = span)
    (hm : s.memory = heap base bytes true frame) (hv : (heap base bytes true frame).valid = true)
    (ha : base.toNat%8 = 0) (hb : 32 ≤ bytes.size) (hold : StateBytes bytes old)
    (hread : SampleAt s.memory ptr sample) :
    ∃ n t, n ≤ 256 ∧ WriteTrace program 0 base.toNat (base.toNat+32) n (atPC s 65536) t ∧
      t.pc = 0 ∧ Output (BitVec.ofNat 64 (rawUpdate old sample drift span).1.code) 0 0 t ∧
        t.memory = heap base (rawBytes old sample drift span bytes) true frame := by
  by_cases hlim : drift = 0 ∨ span = 0 ∨ drift < span
  · simp only [BitVec.ofNat_eq_ofNat] at hlim
    obtain ⟨n, t, hn, ht, hp, ho⟩ := invalid_limits_trace s hra (by simpa [hd, hspan] using hlim)
    exact ⟨n, t, hn, ht.empty_reframe _ _, hp, by simpa [rawUpdate, hlim, Spec.Clock.Status.code] using ho,
      by simpa [rawBytes, hlim] using ht.empty_memory.trans hm⟩
  simp only [BitVec.ofNat_eq_ofNat] at hlim
  have hdn : drift ≠ 0 := fun h => hlim (Or.inl h)
  have hsn : span ≠ 0 := fun h => hlim (Or.inr (Or.inl h))
  have hle : span ≤ drift := BitVec.not_lt.mp (fun h => hlim (Or.inr (Or.inr h)))
  have hstate : StateAt s.memory (s.getReg .x10) old := by
    rw [hbase, hm]; exact stateBytes_owned base bytes frame old hv ha hb hold
  by_cases hvalid : validRaw old
  case neg =>
    obtain ⟨n, t, hn, ht, hp, ho⟩ := invalid_state_trace s old hra (by simpa [hm] using hv) hstate
      (by simpa [hd] using hdn) (by simpa [hspan] using hsn) (by simpa [hd, hspan] using hle) (invalid_raw old hvalid)
    exact ⟨n, t, hn, ht.empty_reframe _ _, hp, by simpa [rawUpdate, hlim, hvalid, Spec.Clock.Status.code] using ho,
      by simpa [rawBytes, hlim, hvalid] using ht.empty_memory.trans hm⟩
  by_cases hmode3 : old.mode = 3
  · obtain ⟨n, t, hn, ht, hp, ho⟩ := stopped_trace s old hra (by simpa [hm] using hv) hstate
      (by simpa [hd] using hdn) (by simpa [hspan] using hsn) (by simpa [hd, hspan] using hle) hmode3
    exact ⟨n, t, hn, ht.empty_reframe _ _, hp, by simpa [rawUpdate, hlim, hvalid, hmode3, Spec.Clock.Status.code] using ho,
      by simpa [rawBytes, hlim, hvalid, hmode3] using ht.empty_memory.trans hm⟩
  simp only [BitVec.ofNat_eq_ofNat] at hmode3
  obtain ⟨n, a, hn, ht, hp, hr, hma, hra'⟩ := valid_state_prefix s old (by simpa [hm] using hv) hstate
    (by simpa [hd] using hdn) (by simpa [hspan] using hsn) (by simpa [hd, hspan] using hle) hvalid.1 hvalid.2 hmode3
  obtain ⟨ns, t, hns, hts, hps, hos, hms⟩ := sample_trace a old sample base ptr drift span bytes frame (hra'.trans hra)
    (by simpa [hbase, hptr, hd, hspan] using hr) (hma.trans hm) hv ha hb (by simpa [hma] using hread)
  refine ⟨n+ns, t, by omega, chain (ht.empty_reframe _ _) hp hts, hps, ?_, ?_⟩
  · rw [raw_status_after_checks old sample drift span hlim hvalid hmode3]
    exact hos
  · simpa [rawBytes, hlim, hvalid, hmode3, afterSampleBytes, checkedBytes] using hms

end Libp2pAsm.Refinement.Clock
