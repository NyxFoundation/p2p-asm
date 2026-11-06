import Libp2pAsm.Refinement.Clock.Sample

namespace Libp2pAsm.Refinement.Clock

open Rv64 Rv64.Logic AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem candidate_trace (s : State) (old : RawState) (sample : RawSample) (base ptr drift span : Word)
    (bytes : Array UInt8) (frame : List Region) (hra : s.getReg .x1 = 0)
    (hr : SampleReady s old sample base ptr drift span) (hm : s.memory = heap base bytes true frame)
    (hv : (heap base bytes true frame).valid = true) (ha : base.toNat%8 = 0) (hb : 32 ≤ bytes.size)
    (hmode2 : old.mode = 2) :
    ∃ n t, n ≤ 11 ∧ WriteTrace program 0 base.toNat (base.toNat+32) n (atPC s 66048) t ∧
      t.pc = 0 ∧ Output 1 0 0 t ∧ t.memory = heap base (sampleBytes bytes 4 sample) true frame := by
  obtain ⟨⟨hbase, hmode, hold, holdseconds, holdnanos, hbillion, hptr, hdrift, hspan⟩,
    hseconds, hnanos, hafter⟩ := hr
  clock_store_facts base bytes frame hv ha hb
  clock_mutation_finish 11

/-- Mode 0 ignores the previous wall timestamp entirely. -/
theorem initial_trace (s : State) (old : RawState) (sample : RawSample) (base ptr drift span : Word)
    (bytes : Array UInt8) (frame : List Region) (hra : s.getReg .x1 = 0)
    (hr : SampleReady s old sample base ptr drift span) (hm : s.memory = heap base bytes true frame)
    (hv : (heap base bytes true frame).valid = true) (ha : base.toNat%8 = 0) (hb : 32 ≤ bytes.size)
    (hmode0 : old.mode = 0) :
    ∃ n t, n ≤ 14 ∧ WriteTrace program 0 base.toNat (base.toNat+32) n (atPC s 66048) t ∧
      t.pc = 0 ∧ Output 0 0 0 t ∧
        t.memory = heap base (writeLE64 (sampleBytes bytes 4 sample) 0 1) true frame := by
  obtain ⟨⟨hbase, hmode, hold, holdseconds, holdnanos, hbillion, hptr, hdrift, hspan⟩,
    hseconds, hnanos, hafter⟩ := hr
  clock_store_facts base bytes frame hv ha hb
  clock_mutation_finish 14

theorem anchor_prefix (s : State) (old : RawState) (sample : RawSample) (base ptr drift span : Word)
    (bytes : Array UInt8) (frame : List Region)
    (hr : SampleReady s old sample base ptr drift span) (hm : s.memory = heap base bytes true frame)
    (hv : (heap base bytes true frame).valid = true) (ha : base.toNat%8 = 0) (hb : 32 ≤ bytes.size)
    (hmode0 : old.mode ≠ 0) (hmode2 : old.mode ≠ 2) :
    ∃ t, WriteTrace program 0 base.toNat (base.toNat+32) 8 (atPC s 66048) t ∧ t.pc = 66128 ∧
      SampleReady t old sample base ptr drift span ∧
      t.memory = heap base (sampleBytes bytes 4 sample) true frame ∧ t.getReg .x1 = s.getReg .x1 := by
  obtain ⟨⟨hbase, hmode, hold, holdseconds, holdnanos, hbillion, hptr, hdrift, hspan⟩,
    hseconds, hnanos, hafter⟩ := hr
  clock_store_facts base bytes frame hv ha hb
  apply Exists.intro
  refine ⟨?trace, ?pc, ?inv, ?memory, ?ra⟩
  case trace =>
    repeat clock_write_step
    exact .nil _
  all_goals simp_all [SampleReady, Ready, sampleBytes, getReg_setReg]

end Libp2pAsm.Refinement.Clock
