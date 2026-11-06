import Libp2pAsm.Refinement.Clock.StateSpec
import Libp2pAsm.Refinement.AsmCodec.Relocation

namespace Libp2pAsm.Refinement.Clock

open Rv64 Rv64.Logic AsmCodec

theorem trace_returns {whole : Program} {entry : Word} {start n : Nat} {s t : State}
    (hi : Invocation program whole entry (s.getReg .x1) start s.memory) (hpc : s.pc = entry)
    (hn : n ≤ 256) (ht : Trace program 0 n (proofEntry s) t) (hret : t.pc = 0) :
    Returns whole (relocated program entry) (s.getReg .x1) 256 s
      ⟨relocateState program entry (s.getReg .x1) t, n⟩ := by
  have hentry := relocate_proofEntry program s entry rfl hpc
  have hleaf := ht.relocate leaf_layout hi.placement (proofEntry_ra s)
  rw [hentry] at hleaf
  have hwhole := hleaf.embed hi.slice hi.image.aligned hi.image.bounded
  have hfinish : (relocateState program entry (s.getReg .x1) t).pc = s.getReg .x1 := by
    simp [relocateState, hret, relocatePC]
  have hcallee := remap_callee (f := relocatePC (entry-program.base) (s.getReg .x1))
    (ra := s.getReg .x1) (callee_saved ht)
  change PreservesCallee (relocateState program entry (s.getReg .x1) (proofEntry s)) _ at hcallee
  rw [hentry] at hcallee
  exact ⟨hwhole.runUntil hfinish hi.image.valid 256 hn, hn, hfinish,
    by simp [relocateState], hcallee,
    fun k u hk hp => hleaf.embed_prefix_inCode hi.slice hi.image.aligned hi.image.bounded hk hp⟩

/-- Failure atomicity includes an empty actual-store trace, not only equal final bytes. -/
def ReadOnlyReturn (whole : Program) (entry : Word) (s : State) (status : Spec.Clock.Status) : Prop :=
  ∃ done, Returns whole (relocated program entry) (s.getReg .x1) 256 s done ∧
    Output (BitVec.ofNat 64 status.code) 0 0 done.state ∧ done.state.memory = s.memory ∧
    WriteTrace whole (s.getReg .x1) 0 0 done.steps s done.state

theorem readonly_return {whole : Program} {entry : Word} {start : Nat} {s : State}
    {status : Spec.Clock.Status}
    (hi : Invocation program whole entry (s.getReg .x1) start s.memory) (hpc : s.pc = entry)
    (ht : ∃ n t, n ≤ 256 ∧ WriteTrace program 0 0 0 n (atPC (proofEntry s) 65536) t ∧
      t.pc = 0 ∧ Output (BitVec.ofNat 64 status.code) 0 0 t) :
    ReadOnlyReturn whole entry s status := by
  obtain ⟨n, t, hn, ht, hret, hout⟩ := ht
  have hw : WriteTrace program 0 0 0 n (proofEntry s) t := by
    simpa only [proofEntry, atPC_atPC] using ht
  have he := (hw.relocate leaf_layout hi.placement (proofEntry_ra s)).embed
    hi.slice hi.image.aligned hi.image.bounded
  rw [relocate_proofEntry program s entry rfl hpc] at he
  refine ⟨⟨relocateState program entry (s.getReg .x1) t, n⟩,
    trace_returns hi hpc hn hw.trace hret, ?_, he.empty_memory, he⟩
  simpa [Output, relocateState] using hout

theorem invalid_limits_embedded (whole : Program) (entry : Word) (start : Nat) (s : State)
    (old : Spec.Clock.State) (sample : Spec.Clock.Sample)
    (hi : Invocation program whole entry (s.getReg .x1) start s.memory) (hpc : s.pc = entry)
    (hbad : s.getReg .x12 = 0 ∨ s.getReg .x13 = 0 ∨ s.getReg .x12 < s.getReg .x13) :
    ReadOnlyReturn whole entry s .invalidLimits ∧
    Spec.Clock.update old sample (s.getReg .x12).toNat (s.getReg .x13).toNat = (.invalidLimits, old) := by
  refine ⟨readonly_return hi hpc ?_, invalid_limits_spec old sample _ _ hbad⟩
  apply invalid_limits_trace _ (proofEntry_ra s)
  simpa using hbad

theorem invalid_state_embedded (whole : Program) (entry : Word) (start : Nat) (s : State)
    (old : RawState) (sample : Spec.Clock.Sample)
    (hi : Invocation program whole entry (s.getReg .x1) start s.memory) (hpc : s.pc = entry)
    (hstate : StateAt s.memory (s.getReg .x10) old)
    (hd : s.getReg .x12 ≠ 0) (hs : s.getReg .x13 ≠ 0) (hle : s.getReg .x13 ≤ s.getReg .x12)
    (hbad : ¬old.mode ≤ 4 ∨ ((old.mode = 1 ∨ old.mode = 4) ∧ ¬old.nanos < 1000000000)) :
    ReadOnlyReturn whole entry s .invalidState ∧
    Spec.Clock.update old.toSpec sample (s.getReg .x12).toNat (s.getReg .x13).toNat =
      (.invalidState, old.toSpec) := by
  refine ⟨readonly_return hi hpc ?_, invalid_state_spec old sample _ _ hd hs hle hbad⟩
  exact invalid_state_trace (proofEntry s) old (proofEntry_ra s) hi.image.memory
    (by simpa using hstate) (by simpa using hd) (by simpa using hs) (by simpa using hle) hbad

theorem stopped_embedded (whole : Program) (entry : Word) (start : Nat) (s : State)
    (old : RawState) (sample : Spec.Clock.Sample)
    (hi : Invocation program whole entry (s.getReg .x1) start s.memory) (hpc : s.pc = entry)
    (hstate : StateAt s.memory (s.getReg .x10) old)
    (hd : s.getReg .x12 ≠ 0) (hs : s.getReg .x13 ≠ 0) (hle : s.getReg .x13 ≤ s.getReg .x12)
    (hmode : old.mode = 3) :
    ReadOnlyReturn whole entry s .monotonicFailure ∧
    Spec.Clock.update old.toSpec sample (s.getReg .x12).toNat (s.getReg .x13).toNat =
      (.monotonicFailure, old.toSpec) := by
  refine ⟨readonly_return hi hpc ?_, stopped_spec old sample _ _ hd hs hle hmode⟩
  exact stopped_trace (proofEntry s) old (proofEntry_ra s) hi.image.memory
    (by simpa using hstate) (by simpa using hd) (by simpa using hs) (by simpa using hle) hmode

end Libp2pAsm.Refinement.Clock
