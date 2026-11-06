import Libp2pAsm.Refinement.Clock.Symbolic

namespace Libp2pAsm.Refinement.Clock

open Rv64 Rv64.Logic AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem stop_trace (s : State) (old : RawState) (sample : RawSample) (base ptr drift span : Word)
    (bytes : Array UInt8) (frame : List Region) (hra : s.getReg .x1 = 0)
    (hr : Ready s old base ptr drift span) (hm : s.memory = heap base bytes true frame)
    (hv : (heap base bytes true frame).valid = true) (ha : base.toNat%8 = 0) (hb : 32 ≤ bytes.size)
    (hread : SampleAt s.memory ptr sample)
    (hbad : ¬sample.status < 2 ∨ ¬sample.beforeNs ≤ sample.afterNs ∨
      (old.mode ≠ 0 ∧ ¬old.afterNs ≤ sample.beforeNs)) :
    ∃ n t, n ≤ 16 ∧ WriteTrace program 0 base.toNat (base.toNat+32) n (atPC s 65760) t ∧
      t.pc = 0 ∧ Output 2 0 0 t ∧ t.memory = heap base (stopBytes bytes) true frame := by
  have hs := hread.2.1.load (by simpa [hm] using hv)
  have hbefore := hread.2.2.1.load (by simpa [hm] using hv)
  have hafter := hread.2.2.2.1.load (by simpa [hm] using hv)
  obtain ⟨hbase, hmode, hold, hseconds, hnanos, hbillion, hptr, hdrift, hspan⟩ := hr
  clock_store_facts base bytes frame hv ha hb
  by_cases hst : sample.status < 2
  case neg => clock_mutation_finish 13
  by_cases hnow : sample.beforeNs ≤ sample.afterNs
  case neg => clock_mutation_finish 14
  obtain ⟨hnonzero, hprevious⟩ := (hbad.resolve_left (not_not_intro hst)).resolve_left (not_not_intro hnow)
  clock_mutation_finish 16

end Libp2pAsm.Refinement.Clock
