import Libp2pAsm.Refinement.Clock.WallTrace
import Libp2pAsm.Refinement.Clock.Stop
import Libp2pAsm.Refinement.Clock.SpecGuards

namespace Libp2pAsm.Refinement.Clock

open Rv64 Rv64.Logic AsmCodec

def sampleStatus (old : RawState) (sample : RawSample) (drift span : Word) : Word :=
  if monotonicBad old sample then 2 else if wallBad sample span then 1 else checkedStatus old sample drift

def afterSampleBytes (old : RawState) (sample : RawSample) (drift span : Word) (bytes : Array UInt8) : Array UInt8 :=
  if monotonicBad old sample then stopBytes bytes
  else if wallBad sample span then unavailableBytes bytes sample else checkedBytes old sample drift bytes

theorem sample_trace (s : State) (old : RawState) (sample : RawSample) (base ptr drift span : Word)
    (bytes : Array UInt8) (frame : List Region) (hra : s.getReg .x1 = 0)
    (hr : Ready s old base ptr drift span) (hm : s.memory = heap base bytes true frame)
    (hv : (heap base bytes true frame).valid = true) (ha : base.toNat%8 = 0) (hb : 32 ≤ bytes.size)
    (hread : SampleAt s.memory ptr sample) :
    ∃ n t, n ≤ 96 ∧ WriteTrace program 0 base.toNat (base.toNat+32) n (atPC s 65760) t ∧
      t.pc = 0 ∧ Output (sampleStatus old sample drift span) 0 0 t ∧
        t.memory = heap base (afterSampleBytes old sample drift span bytes) true frame := by
  by_cases hmono : monotonicBad old sample
  · obtain ⟨n, t, hn, ht, hp, ho, hmem⟩ := stop_trace s old sample base ptr drift span bytes frame hra hr hm hv ha hb hread hmono
    exact ⟨n, t, by omega, ht, hp, by simpa [sampleStatus, hmono] using ho,
      by simpa [afterSampleBytes, hmono] using hmem⟩
  obtain ⟨hst, hnow, hprev⟩ := monotonic_good hmono
  by_cases hwall : wallBad sample span
  · obtain ⟨n, t, hn, ht, hp, ho, hmem⟩ := unavailable_trace s old sample base ptr drift span bytes frame hra hr hm hv ha hb
      hread hst hnow hprev hwall
    exact ⟨n, t, by omega, ht, hp, by simpa [sampleStatus, hmono, hwall] using ho,
      by simpa [afterSampleBytes, hmono, hwall] using hmem⟩
  obtain ⟨hst0, hwidth, hnanos⟩ := wall_good hwall
  obtain ⟨n, a, hn, ht, hp, hr', hma, hra'⟩ := valid_sample_prefix s old sample base ptr drift span hr
    (by simpa [hm] using hv) hread hst0 hnow hprev hwidth hnanos
  obtain ⟨nw, t, hnw, htw, hpw, how, hmw⟩ := wall_trace a old sample base ptr drift span bytes frame
    (hra'.trans hra) hr' (hma.trans hm) hv ha hb
  exact ⟨n+nw, t, by omega, chain (ht.empty_reframe _ _) hp htw, hpw,
    by simpa [sampleStatus, hmono, hwall] using how,
    by simpa [afterSampleBytes, hmono, hwall] using hmw⟩

end Libp2pAsm.Refinement.Clock
