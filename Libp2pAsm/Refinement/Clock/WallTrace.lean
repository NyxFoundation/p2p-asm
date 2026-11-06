import Libp2pAsm.Refinement.Clock.Difference
import Libp2pAsm.Refinement.Clock.Raw

namespace Libp2pAsm.Refinement.Clock

open Rv64 Rv64.Logic AsmCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem chain {p stop lo hi n m s a t pc}
    (h : WriteTrace p stop lo hi n s a) (hp : a.pc = pc)
    (k : WriteTrace p stop lo hi m (atPC a pc) t) : WriteTrace p stop lo hi (n+m) s t :=
  h.append (writeTrace_at_pc hp k)

def checkedStatus (old : RawState) (sample : RawSample) (drift : Word) : Word :=
  if old.mode = 2 then 1 else if old.mode = 0 ∨ coherent old sample drift then 0 else 1

def checkedBytes (old : RawState) (sample : RawSample) (drift : Word) (bytes : Array UInt8) : Array UInt8 :=
  if old.mode = 2 then sampleBytes bytes 4 sample
  else if old.mode = 0 ∨ coherent old sample drift then writeLE64 (sampleBytes bytes 4 sample) 0 1
  else sampleBytes bytes 4 sample

theorem wall_trace (s : State) (old : RawState) (sample : RawSample) (base ptr drift span : Word)
    (bytes : Array UInt8) (frame : List Region) (hra : s.getReg .x1 = 0)
    (hr : SampleReady s old sample base ptr drift span) (hm : s.memory = heap base bytes true frame)
    (hv : (heap base bytes true frame).valid = true) (ha : base.toNat%8 = 0) (hb : 32 ≤ bytes.size) :
    ∃ n t, n ≤ 64 ∧ WriteTrace program 0 base.toNat (base.toNat+32) n (atPC s 66048) t ∧
      t.pc = 0 ∧ Output (checkedStatus old sample drift) 0 0 t ∧
        t.memory = heap base (checkedBytes old sample drift bytes) true frame := by
  by_cases hm2 : old.mode = 2
  · obtain ⟨n, t, hn, ht, hp, ho, hmem⟩ := candidate_trace s old sample base ptr drift span bytes frame hra hr hm hv ha hb hm2
    exact ⟨n, t, by omega, ht, hp, by simpa [checkedStatus, hm2] using ho, by simpa [checkedBytes, hm2] using hmem⟩
  by_cases hm0 : old.mode = 0
  · obtain ⟨n, t, hn, ht, hp, ho, hmem⟩ := initial_trace s old sample base ptr drift span bytes frame hra hr hm hv ha hb hm0
    exact ⟨n, t, by omega, ht, hp, by simpa [checkedStatus, hm2, hm0] using ho,
      by simpa [checkedBytes, hm2, hm0] using hmem⟩
  simp only [BitVec.ofNat_eq_ofNat] at hm2 hm0
  obtain ⟨a, ht, hp, hr', hmem, hra'⟩ := anchor_prefix s old sample base ptr drift span bytes frame hr hm hv ha hb hm0 hm2
  have har : a.getReg .x1 = 0 := hra'.trans hra
  by_cases hback : wallBackwards old sample
  · obtain ⟨n, t, hn, htail, hpc, hout, hmemory⟩ := backwards_wall_trace a old sample base ptr drift span har hr' hback
    refine ⟨8+n, t, by omega, chain ht hp (htail.empty_reframe _ _), hpc, ?_, ?_⟩
    · simpa [checkedStatus, hm2, hm0, coherent, hback] using hout
    · simpa [checkedBytes, hm2, hm0, coherent, hback] using hmemory.trans hmem
  have hs : old.seconds.toInt ≤ sample.seconds.toInt := by have h := hback; unfold wallBackwards at h; omega
  have he : sample.seconds = old.seconds → old.nanos ≤ sample.nanos := by
    intro heq
    by_cases hle : old.nanos ≤ sample.nanos
    · exact hle
    · exact False.elim (hback (Or.inr ⟨heq, hle⟩))
  obtain ⟨ne, e, hne, hte, hpe, hre, hme, hrae⟩ := elapsed_prefix a old sample base ptr drift span hr' hs he
  have hvc : (heap base (sampleBytes bytes 4 sample) true frame).valid = true := by
    rw [heap_valid_congr base _ bytes true frame (by simp)]; exact hv
  obtain ⟨nd, t, hnd, htd, hpd, hod, hmd⟩ := difference_trace e base _ _ _ drift _ frame (hrae.trans har) hre
    (hme.trans hmem) hvc ha (by simpa using hb)
  refine ⟨8+ne+nd, t, by omega, chain (chain ht hp (hte.empty_reframe _ _)) hpe htd, hpd, ?_, ?_⟩
  · simpa [checkedStatus, hm2, hm0, coherent, hback] using hod
  · simpa [checkedBytes, hm2, hm0, coherent, hback] using hmd

end Libp2pAsm.Refinement.Clock
