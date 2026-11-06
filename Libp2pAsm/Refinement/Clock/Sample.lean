import Libp2pAsm.Refinement.Clock.Symbolic

namespace Libp2pAsm.Refinement.Clock

open Rv64 Rv64.Logic AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

theorem unavailable_trace (s : State) (old : RawState) (sample : RawSample) (base ptr drift span : Word)
    (bytes : Array UInt8) (frame : List Region) (hra : s.getReg .x1 = 0)
    (hr : Ready s old base ptr drift span) (hm : s.memory = heap base bytes true frame)
    (hv : (heap base bytes true frame).valid = true) (ha : base.toNat%8 = 0) (hb : 32 ≤ bytes.size)
    (hread : SampleAt s.memory ptr sample) (hst : sample.status < 2)
    (hnow : sample.beforeNs ≤ sample.afterNs) (hprev : old.mode ≠ 0 → old.afterNs ≤ sample.beforeNs)
    (hbad : sample.status ≠ 0 ∨ ¬sample.afterNs-sample.beforeNs ≤ span ∨ ¬sample.nanos < 1000000000) :
    ∃ n t, n ≤ 24 ∧ WriteTrace program 0 base.toNat (base.toNat+32) n (atPC s 65760) t ∧
      t.pc = 0 ∧ Output 1 0 0 t ∧ t.memory = heap base (unavailableBytes bytes sample) true frame := by
  have hs := hread.2.1.load (by simpa [hm] using hv)
  have hbefore := hread.2.2.1.load (by simpa [hm] using hv)
  have hafter := hread.2.2.2.1.load (by simpa [hm] using hv)
  have hseconds := hread.2.2.2.2.1.load (by simpa [hm] using hv)
  have hnanos := hread.2.2.2.2.2.load (by simpa [hm] using hv)
  obtain ⟨hbase, hmode, hold, holdseconds, holdnanos, hbillion, hptr, hdrift, hspan⟩ := hr
  clock_store_facts base bytes frame hv ha hb
  by_cases hst0 : sample.status = 0
  case neg =>
    by_cases hm0 : old.mode = 0
    · clock_mutation_finish 17
    · have hp := hprev hm0
      clock_mutation_finish 19
  by_cases hwidth : sample.afterNs-sample.beforeNs ≤ span
  case neg =>
    by_cases hm0 : old.mode = 0
    · clock_mutation_finish 19
    · have hp := hprev hm0
      clock_mutation_finish 21
  have hns : ¬sample.nanos < 1000000000 :=
    (hbad.resolve_left (not_not_intro hst0)).resolve_left (not_not_intro hwidth)
  by_cases hm0 : old.mode = 0
  · clock_mutation_finish 22
  · have hp := hprev hm0
    clock_mutation_finish 24

def SampleReady (s : State) (old : RawState) (sample : RawSample) (base ptr drift span : Word) : Prop :=
  Ready s old base ptr drift span ∧ s.getReg .x14 = sample.seconds ∧
    s.getReg .x15 = sample.nanos ∧ s.getReg .x31 = sample.afterNs

macro "clock_sample_finish " n:term : tactic => `(tactic| (
  simp only [BitVec.ofNat_eq_ofNat] at *
  refine ⟨$n, ?_⟩
  apply Exists.intro
  refine ⟨by decide, ?trace, ?pc, ?inv, ?memory, ?ra⟩
  case trace =>
    repeat clock_read_step
    exact .nil _
  all_goals simp_all [SampleReady, Ready, getReg_setReg]))

theorem valid_sample_prefix (s : State) (old : RawState) (sample : RawSample) (base ptr drift span : Word)
    (hr : Ready s old base ptr drift span) (hm : s.memory.valid = true) (hread : SampleAt s.memory ptr sample)
    (hst : sample.status = 0) (hnow : sample.beforeNs ≤ sample.afterNs)
    (hprev : old.mode ≠ 0 → old.afterNs ≤ sample.beforeNs)
    (hwidth : sample.afterNs-sample.beforeNs ≤ span) (hns : sample.nanos < 1000000000) :
    ∃ n t, n ≤ 15 ∧ WriteTrace program 0 0 0 n (atPC s 65760) t ∧ t.pc = 66048 ∧
      SampleReady t old sample base ptr drift span ∧ t.memory = s.memory ∧ t.getReg .x1 = s.getReg .x1 := by
  have hs := hread.2.1.load hm
  have hbefore := hread.2.2.1.load hm
  have hafter := hread.2.2.2.1.load hm
  have hseconds := hread.2.2.2.2.1.load hm
  have hnanos := hread.2.2.2.2.2.load hm
  obtain ⟨hbase, hmode, hold, holdseconds, holdnanos, hbillion, hptr, hdrift, hspan⟩ := hr
  by_cases hm0 : old.mode = 0
  · clock_sample_finish 13
  · have hp := hprev hm0
    clock_sample_finish 15

end Libp2pAsm.Refinement.Clock
