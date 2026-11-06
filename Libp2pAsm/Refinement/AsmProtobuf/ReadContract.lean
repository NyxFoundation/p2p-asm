import Libp2pAsm.Refinement.AsmProtobuf.ReadBounds

namespace Libp2pAsm.Refinement.AsmProtobuf
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmCodec Footprint

def CodeSeparated (whole : Program) (ptr len : Word) : Prop :=
  ptr.toNat+len.toNat ≤ 2^64 → len ≠ 0 →
    ptr.toNat+len.toNat ≤ whole.base.toNat ∨ whole.base.toNat+4*whole.code.size ≤ ptr.toNat

theorem platform_registers {stop n s t} (h : Trace program stop n s t) :
    t.getReg .x3=s.getReg .x3 ∧ t.getReg .x4=s.getReg .x4 := by
  constructor <;> apply h.register_frame <;> decide

/-- Exact actual loads, total raw-ABI correspondence, memory frame and arbitrary embedding.
Metadata failures perform zero loads; content paths load only the consumed scan prefix. -/
theorem decode_with_footprint (whole : Program) (entry : Word) (start : Nat)
    (s : State) (bytes : List UInt8)
    (hi : Invocation program whole entry (s.getReg .x1) start s.memory) (hpc : s.pc=entry)
    (hbytes : InputAt s bytes) (_hsep : CodeSeparated whole (s.getReg .x10) (s.getReg .x11)) :
    ∃ done, Returns whole (relocated program entry) (s.getReg .x1) 256 s done ∧
      RawPost (s.getReg .x10) (s.getReg .x11) bytes done.state ∧
      done.state.memory=s.memory ∧
      ReadTrace whole (s.getReg .x1) (rawReads (s.getReg .x10) (s.getReg .x11) bytes)
        done.steps s done.state ∧
      WriteTrace whole (s.getReg .x1) 0 0 done.steps s done.state ∧
      done.state.getReg .x3=s.getReg .x3 ∧ done.state.getReg .x4=s.getReg .x4 := by
  obtain ⟨n,t,hn,ht,hret,hout⟩ := Footprint.raw_trace (proofEntry s) bytes (proofEntry_ra s)
    (by simpa using hi.image.memory) (by simpa [InputAt] using hbytes)
  have htrace : Trace program 0 n (proofEntry s) t := by
    simpa only [proofEntry,atPC_atPC] using ht.trace
  have hread := (ht.relocate leaf_layout hi.placement (proofEntry_ra s)).embed
    hi.slice hi.image.aligned hi.image.bounded
  have hwrite := ((htrace.noStores no_stores 0 0).relocate leaf_layout hi.placement
    (proofEntry_ra s)).embed hi.slice hi.image.aligned hi.image.bounded
  have hentry := relocate_proofEntry program s entry rfl hpc
  simp only [proofEntry,atPC_atPC] at hread
  change ReadTrace whole _ _ n (relocateState program entry (s.getReg .x1) (proofEntry s)) _ at hread
  rw [hentry] at hread hwrite
  refine ⟨⟨relocateState program entry (s.getReg .x1) t,n⟩,
    trace_returns hi hpc hn htrace hret,?_,?_,?_,hwrite,?_⟩
  · have hh := remap_rawPost (f := relocatePC (entry-program.base) (s.getReg .x1))
      (ra := s.getReg .x1) hout
    simpa [relocateState] using hh
  · simpa only [relocateState,remap_memory,proofEntry_memory] using htrace.memory_frame no_stores
  · simpa [getReg_setReg] using hread
  · simpa [relocateState] using platform_registers htrace

end Libp2pAsm.Refinement.AsmProtobuf
