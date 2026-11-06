import Libp2pAsm.Refinement.AsmDer.Raw
import Libp2pAsm.Refinement.AsmDer.Specification

namespace Libp2pAsm.Refinement.AsmDer
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

theorem trace_returns {whole : Program} {entry : Word} {start n : Nat} {s t : State}
    (hi : Invocation decoder whole entry (s.getReg .x1) start s.memory) (hpc : s.pc = entry)
    (hn : n ≤ 129) (ht : Trace decoder 0 n (proofEntry s) t) (hret : t.pc = 0) :
    Returns whole (relocated decoder entry) (s.getReg .x1) 129 s
      ⟨relocateState decoder entry (s.getReg .x1) t,n⟩ := by
  have hentry := relocate_proofEntry decoder s entry rfl hpc
  have hleaf := ht.relocate decoder_layout hi.placement (proofEntry_ra s)
  rw [hentry] at hleaf
  have hwhole := hleaf.embed hi.slice hi.image.aligned hi.image.bounded
  have hfinish : (relocateState decoder entry (s.getReg .x1) t).pc = s.getReg .x1 := by
    simp [relocateState,hret,relocatePC]
  have hcallee := remap_callee (f := relocatePC (entry-decoder.base) (s.getReg .x1))
    (ra := s.getReg .x1) (callee_saved (Or.inl rfl) ht)
  change PreservesCallee (relocateState decoder entry (s.getReg .x1) (proofEntry s)) _ at hcallee
  rw [hentry] at hcallee
  exact ⟨hwhole.runUntil hfinish hi.image.valid 129 hn,hn,hfinish,
    by simp [relocateState],hcallee,
    fun k u hk hprefix => hleaf.embed_prefix_inCode hi.slice hi.image.aligned hi.image.bounded hk hprefix⟩

theorem remap_cleared {f : Word → Word} {ra : Word} {t : State} (h : DecodeClear t) :
    DecodeClear (remap f ra t) := by
  intro r hr hout
  have hne : r≠.x1 := by intro he; subst r; simp [Asm.Crypto.Sha2.cleared] at hr
  simpa only [remap_get _ _ _ _ hne] using h r hr hout

theorem remap_post {f : Word → Word} {ra : Word} {t : State}
    {result : Except Spec.Codec.Der.Error Spec.Codec.Der.Decoded} (h : DecodePost result t) :
    DecodePost result (remap f ra t) := by
  cases result <;> simpa [DecodePost] using h

theorem remap_rawPost {f : Word → Word} {ra ptr len : Word} {bytes : List UInt8} {t : State}
    (h : RawPost ptr len bytes t) : RawPost ptr len bytes (remap f ra t) :=
  ⟨remap_post h.1,remap_cleared h.2⟩

theorem platform_registers {stop n s t} (h : Trace decoder stop n s t) :
    t.getReg .x3=s.getReg .x3 ∧ t.getReg .x4=s.getReg .x4 := by
  constructor <;> apply h.register_frame <;> decide

/-- Exact actual loads, total raw-ABI correspondence, memory frame and arbitrary embedding.
Metadata failures perform zero loads; content paths load only the consumed scan prefix. -/
theorem decode_with_footprint (whole : Program) (entry : Word) (start : Nat)
    (s : State) (bytes : List UInt8)
    (hi : Invocation decoder whole entry (s.getReg .x1) start s.memory) (hpc : s.pc=entry)
    (hbytes : InputAt s bytes) (_hsep : AsmProtobuf.CodeSeparated whole (s.getReg .x10) (s.getReg .x11)) :
    ∃ done, Returns whole (relocated decoder entry) (s.getReg .x1) 129 s done ∧
      RawPost (s.getReg .x10) (s.getReg .x11) bytes done.state ∧
      done.state.memory=s.memory ∧
      ReadTrace whole (s.getReg .x1) (rawReads (s.getReg .x10) (s.getReg .x11) bytes)
        done.steps s done.state ∧
      WriteTrace whole (s.getReg .x1) 0 0 done.steps s done.state ∧
      done.state.getReg .x3=s.getReg .x3 ∧ done.state.getReg .x4=s.getReg .x4 := by
  obtain ⟨n,t,hn,ht,hret,hout⟩ := raw_trace (proofEntry s) bytes (proofEntry_ra s)
    (by simpa using hi.image.memory) (by simpa [InputAt,AsmProtobuf.InputAt] using hbytes)
  have htrace : Trace decoder 0 n (proofEntry s) t := by
    simpa only [proofEntry,atPC_atPC] using ht.trace
  have hread := (ht.relocate decoder_layout hi.placement (proofEntry_ra s)).embed
    hi.slice hi.image.aligned hi.image.bounded
  have hwrite := ((htrace.noStores decoder_no_stores 0 0).relocate decoder_layout hi.placement
    (proofEntry_ra s)).embed hi.slice hi.image.aligned hi.image.bounded
  have hentry := relocate_proofEntry decoder s entry rfl hpc
  simp only [proofEntry,atPC_atPC] at hread
  change ReadTrace whole _ _ n (relocateState decoder entry (s.getReg .x1) (proofEntry s)) _ at hread
  rw [hentry] at hread hwrite
  refine ⟨⟨relocateState decoder entry (s.getReg .x1) t,n⟩,
    trace_returns hi hpc hn htrace hret,?_,?_,?_,hwrite,?_⟩
  · have hh := remap_rawPost (f := relocatePC (entry-decoder.base) (s.getReg .x1))
      (ra := s.getReg .x1) hout
    simpa [relocateState] using hh
  · simpa only [relocateState,remap_memory,proofEntry_memory] using htrace.memory_frame decoder_no_stores
  · simpa [getReg_setReg] using hread
  · simpa [relocateState] using platform_registers htrace

end Libp2pAsm.Refinement.AsmDer
