import Libp2pAsm.Refinement.Clock.Execution
import Libp2pAsm.Refinement.Clock.EarlyContract

namespace Libp2pAsm.Refinement.Clock

open Rv64 Rv64.Logic AsmCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- Full raw-domain correspondence. Correlation of observations with real time is a
caller obligation; the machine/SPEC equality also covers every rejected raw sample. -/
theorem check_embedded (whole : Program) (entry : Word) (start : Nat) (s : State)
    (old : RawState) (sample : RawSample) (bytes : Array UInt8) (frame : List Region)
    (hi : Invocation program whole entry (s.getReg .x1) start s.memory) (hpc : s.pc = entry)
    (hm : s.memory = heap (s.getReg .x10) bytes true frame)
    (ha : (s.getReg .x10).toNat%8 = 0) (hb : 32 ≤ bytes.size) (hold : StateBytes bytes old)
    (hread : SampleAt s.memory (s.getReg .x11) sample)
    (_hdisjoint : (s.getReg .x10).toNat+32 ≤ (s.getReg .x11).toNat ∨
      (s.getReg .x11).toNat+40 ≤ (s.getReg .x10).toNat) :
    ∃ (done : Completed) (after : RawState) (outBytes : Array UInt8),
      Returns whole (relocated program entry) (s.getReg .x1) 256 s done ∧
      Output (BitVec.ofNat 64 (Spec.Clock.update old.toSpec sample.toSpec
        (s.getReg .x12).toNat (s.getReg .x13).toNat).1.code) 0 0 done.state ∧
      after.toSpec = (Spec.Clock.update old.toSpec sample.toSpec
        (s.getReg .x12).toNat (s.getReg .x13).toNat).2 ∧
      StateAt done.state.memory (s.getReg .x10) after ∧
      done.state.memory = heap (s.getReg .x10) outBytes true frame ∧
      ByteFrame 0 32 bytes outBytes ∧
      WriteTrace whole (s.getReg .x1) (s.getReg .x10).toNat ((s.getReg .x10).toNat+32) done.steps s done.state := by
  have hv : (heap (s.getReg .x10) bytes true frame).valid = true := by rw [← hm]; exact hi.image.memory
  obtain ⟨n, t, hn, ht, hret, hout, hmem⟩ := raw_trace (proofEntry s) old sample
    (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13) bytes frame
    (proofEntry_ra s) (by simp) (by simp) (by simp) (by simp) (by simpa using hm) hv ha hb hold (by simpa using hread)
  have hwt : WriteTrace program 0 (s.getReg .x10).toNat ((s.getReg .x10).toNat+32) n (proofEntry s) t := by
    simpa only [proofEntry, atPC_atPC] using ht
  have he := (hwt.relocate leaf_layout hi.placement (proofEntry_ra s)).embed
    hi.slice hi.image.aligned hi.image.bounded
  rw [relocate_proofEntry program s entry rfl hpc] at he
  have hpost := rawBytes_post old sample (s.getReg .x12) (s.getReg .x13) bytes hb hold
  have hrefine := raw_refines_spec old sample (s.getReg .x12) (s.getReg .x13)
  refine ⟨⟨relocateState program entry (s.getReg .x1) t, n⟩,
    (rawUpdate old sample (s.getReg .x12) (s.getReg .x13)).2,
    rawBytes old sample (s.getReg .x12) (s.getReg .x13) bytes,
    trace_returns hi hpc hn hwt.trace hret, ?_, ?_, ?_, ?_, hpost.2, he⟩
  · rw [hrefine]
    simpa [Output, relocateState] using hout
  · exact (congrArg Prod.snd hrefine).symm
  · have hv' : (heap (s.getReg .x10) (rawBytes old sample (s.getReg .x12) (s.getReg .x13) bytes) true frame).valid = true := by
      rw [heap_valid_congr _ _ bytes true frame hpost.2.1.symm]; exact hv
    have hfinal : (relocateState program entry (s.getReg .x1) t).memory =
        heap (s.getReg .x10) (rawBytes old sample (s.getReg .x12) (s.getReg .x13) bytes) true frame := by
      simpa [relocateState] using hmem
    rw [hfinal]
    exact stateBytes_owned _ _ frame _ hv' ha (by rw [← hpost.2.1]; exact hb) hpost.1
  · simpa [relocateState] using hmem

end Libp2pAsm.Refinement.Clock
