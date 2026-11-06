import Libp2pAsm.Refinement.AsmBuffer.Execution
import Libp2pAsm.Refinement.AsmBuffer.Specification
import Libp2pAsm.Refinement.AsmCodec.Relocation

namespace Libp2pAsm.Refinement.AsmBuffer

open Rv64 Rv64.Logic AsmCodec

/-- A buffer invocation returns with the full ABI frame and never fetches surrounding code. -/
theorem trace_returns {whole : Program} {entry : Word} {start n : Nat} {s t : State}
    (hi : Invocation program whole entry (s.getReg .x1) start s.memory) (hpc : s.pc = entry)
    (hn : n ≤ 96) (ht : Trace program 0 n (proofEntry s) t) (hret : t.pc = 0) :
    Returns whole (relocated program entry) (s.getReg .x1) 96 s
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
  exact ⟨hwhole.runUntil hfinish hi.image.valid 96 hn, hn, hfinish,
    by simp [relocateState], hcallee,
    fun k u hk hprefix => hleaf.embed_prefix_inCode hi.slice hi.image.aligned hi.image.bounded hk hprefix⟩

/-- Universal fetch/ASM/SPEC refinement, including every raw-ABI rejection.
The caller supplies actual owned reference/descriptor bytes; resolution need not succeed.
The returned empty WriteTrace forbids even stores of unchanged values. -/
theorem resolve_embedded (whole : Program) (entry : Word) (start : Nat)
    (s : State) (ref : RawReference) (r : RawRegion)
    (hi : Invocation program whole entry (s.getReg .x1) start s.memory) (hpc : s.pc = entry)
    (href : ReferenceAt s.memory (s.getReg .x11) ref)
    (hregion : RegionAt s.memory (s.getReg .x10) (s.getReg .x12) (s.getReg .x13) ref r) :
    ∃ done, Returns whole (relocated program entry) (s.getReg .x1) 96 s done ∧
      RawPost (specOutput (abiSpec (s.getReg .x10) (s.getReg .x12) (s.getReg .x13) ref r)) done.state ∧
      done.state.memory = s.memory ∧ WriteTrace whole (s.getReg .x1) 0 0 done.steps s done.state := by
  obtain ⟨n, t, hn, ht, hret, hout⟩ := raw_trace (proofEntry s) ref r (proofEntry_ra s)
    (by simpa using hi.image.memory) (by simpa using href) (by simpa using hregion)
  have htrace : Trace program 0 n (proofEntry s) t := by simpa only [proofEntry, atPC_atPC] using ht
  have hwrite := ((htrace.noStores no_stores 0 0).relocate leaf_layout hi.placement
    (proofEntry_ra s)).embed hi.slice hi.image.aligned hi.image.bounded
  rw [relocate_proofEntry program s entry rfl hpc] at hwrite
  refine ⟨⟨relocateState program entry (s.getReg .x1) t, n⟩,
    trace_returns hi hpc hn htrace hret, ?_, ?_, hwrite⟩
  · simp only [proofEntry_get _ _ (by decide : Reg.x10 ≠ .x1),
      proofEntry_get _ _ (by decide : Reg.x12 ≠ .x1),
      proofEntry_get _ _ (by decide : Reg.x13 ≠ .x1), raw_refines_spec] at hout
    simpa [RawPost, Output, relocateState] using hout
  · simpa only [relocateState, remap_memory, proofEntry_memory] using htrace.memory_frame no_stores

end Libp2pAsm.Refinement.AsmBuffer
