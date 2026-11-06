import Libp2pAsm.Refinement.AsmDer.EncodeFootprint

namespace Libp2pAsm.Refinement.AsmDer.Encode
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

theorem trace_returns {whole : Program} {entry : Word} {start n : Nat} {s t : State}
    (hi : Invocation encoder whole entry (s.getReg .x1) start s.memory) (hpc : s.pc = entry)
    (hn : n ≤ 157) (ht : Trace encoder 0 n (proofEntry s) t) (hret : t.pc = 0) :
    Returns whole (relocated encoder entry) (s.getReg .x1) 157 s
      ⟨relocateState encoder entry (s.getReg .x1) t,n⟩ := by
  have hentry := relocate_proofEntry encoder s entry rfl hpc
  have hleaf := ht.relocate encoder_layout hi.placement (proofEntry_ra s)
  rw [hentry] at hleaf
  have hwhole := hleaf.embed hi.slice hi.image.aligned hi.image.bounded
  have hfinish : (relocateState encoder entry (s.getReg .x1) t).pc = s.getReg .x1 := by
    simp [relocateState,hret,relocatePC]
  have hcallee := remap_callee (f := relocatePC (entry-encoder.base) (s.getReg .x1))
    (ra := s.getReg .x1) (callee_saved (Or.inr rfl) ht)
  change PreservesCallee (relocateState encoder entry (s.getReg .x1) (proofEntry s)) _ at hcallee
  rw [hentry] at hcallee
  exact ⟨hwhole.runUntil hfinish hi.image.valid 157 hn,hn,hfinish,
    by simp [relocateState],hcallee,
    fun k u hk hprefix => hleaf.embed_prefix_inCode hi.slice hi.image.aligned hi.image.bounded hk hprefix⟩

theorem remap_clear {f : Word → Word} {ra : Word} {t : State} (h : Clear t) : Clear (remap f ra t) := by
  intro r hr hn
  have hne : r≠.x1 := by intro he; subst r; simp [Asm.Crypto.Sha2.cleared] at hr
  simpa only [remap_get _ _ _ _ hne] using h r hr hn

theorem remap_post {f : Word → Word} {ra : Word} {t : State}
    {res : Except Spec.Codec.Der.Error (List UInt8)} (h : Post res t) : Post res (remap f ra t) := by
  cases res with
  | error e => exact errorOutput_remap h
  | ok bytes => exact ⟨by simpa using h.1,remap_clear h.2⟩

theorem platform_registers {stop n s t} (h : Trace encoder stop n s t) :
    t.getReg .x3=s.getReg .x3 ∧ t.getReg .x4=s.getReg .x4 := by
  constructor <;> apply h.register_frame <;> decide

/-- Universal actual-fetch header encoder, including all raw error priorities.
The only ownership assumption is a structural writable heap on validated metadata.
The exact store list and patch preserve every byte outside the header. -/
theorem encode_embedded (whole : Program) (entry : Word) (start : Nat)
    (s : State) (bytes : Array UInt8) (frame : List Region)
    (hi : Invocation encoder whole entry (s.getReg .x1) start s.memory) (hpc : s.pc=entry)
    (hbytes : InputAt s bytes frame) :
    ∃ done, Returns whole (relocated encoder entry) (s.getReg .x1) 157 s done ∧
      Post (result (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13)) done.state ∧
      MemoryPost s done.state bytes frame (result (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13)) ∧
      AccessTrace whole (s.getReg .x1) [] (rawWrites (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13))
        done.steps s done.state ∧
      WriteTrace whole (s.getReg .x1) (s.getReg .x12).toNat
        ((s.getReg .x12).toNat+headerSize (s.getReg .x11).toNat) done.steps s done.state ∧
      done.state.getReg .x3=s.getReg .x3 ∧ done.state.getReg .x4=s.getReg .x4 := by
  obtain ⟨n,t,hn,ht,hret,hout,hmem⟩ := raw_trace (proofEntry s) bytes frame (proofEntry_ra s)
    (by simpa using hi.image.memory) (by simpa [InputAt] using hbytes)
  have htrace : Trace encoder 0 n (proofEntry s) t := by
    simpa only [proofEntry,atPC_atPC] using ht.trace
  have haccess := (ht.relocate encoder_layout hi.placement (proofEntry_ra s)).embed
    hi.slice hi.image.aligned hi.image.bounded
  have hentry := relocate_proofEntry encoder s entry rfl hpc
  simp only [proofEntry,atPC_atPC] at haccess
  change AccessTrace whole _ _ _ n (relocateState encoder entry (s.getReg .x1) (proofEntry s)) _ at haccess
  rw [hentry] at haccess
  have haccess' : AccessTrace whole (s.getReg .x1) []
      (rawWrites (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13)) n s
      (relocateState encoder entry (s.getReg .x1) t) := by simpa using haccess
  refine ⟨⟨relocateState encoder entry (s.getReg .x1) t,n⟩,trace_returns hi hpc hn htrace hret,
    ?_,?_,haccess',?_,?_⟩
  · simpa [relocateState] using
      (remap_post (f := relocatePC (entry-encoder.base) (s.getReg .x1)) (ra := s.getReg .x1) hout)
  · unfold MemoryPost at hmem ⊢
    simp only [proofEntry_get _ _ (by decide : Reg.x10≠.x1),proofEntry_get _ _ (by decide : Reg.x11≠.x1),
      proofEntry_get _ _ (by decide : Reg.x12≠.x1),proofEntry_get _ _ (by decide : Reg.x13≠.x1)] at hmem
    cases he : result (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13) <;>
      simpa [he,relocateState] using hmem
  · apply haccess'.writeTrace
    intro a ha
    have hb := rawWrites_bounds _ _ _ _ a ha
    simpa only [hb.1] using hb.2
  · simpa [relocateState] using platform_registers htrace

end Libp2pAsm.Refinement.AsmDer.Encode
