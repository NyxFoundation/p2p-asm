import Libp2pAsm.Refinement.AsmProtobuf.Execution

namespace Libp2pAsm.Refinement.AsmProtobuf
open Rv64 Rv64.Logic AsmCodec

/-- Raw pointer/length validation precedes any content inspection. -/
def RawPost (ptr len : Word) (bytes : List UInt8) (t : State) : Prop :=
  if 2^64 < ptr.toNat+len.toNat then Output 4 0 0 t ∧ Cleared t
  else if len = 0 then Post (.error .truncated) t
  else Post (Spec.Codec.ProtobufVarint.decode bytes) t

/-- Empty and wrapping ranges require no owned input region. -/
def InputAt (s : State) (bytes : List UInt8) : Prop :=
  (s.getReg .x10).toNat+(s.getReg .x11).toNat ≤ 2^64 → s.getReg .x11 ≠ 0 →
    (s.getReg .x11).toNat = bytes.length ∧ Parser.BytesAt s.memory (s.getReg .x10) bytes

theorem raw_trace (s : State) (bytes : List UInt8) (hra : s.getReg .x1 = 0)
    (hm : s.memory.valid = true) (hi : InputAt s bytes) :
    ∃ n t, n ≤ 256 ∧ Trace program 0 n (atPC s 65536) t ∧ t.pc = 0 ∧
      RawPost (s.getReg .x10) (s.getReg .x11) bytes t := by
  by_cases hb : 2^64 < (s.getReg .x10).toNat+(s.getReg .x11).toNat
  · obtain ⟨t,ht,hp,ho⟩ := range_error s hra hb
    exact ⟨21,t,by decide,ht,hp,by simpa only [RawPost,if_pos hb] using ho⟩
  by_cases hz : s.getReg .x11 = 0
  · have hs : (s.getReg .x10).toNat+(s.getReg .x11).toNat ≤ 2^64 := by omega
    obtain ⟨n,a,hn,ht,hp,ha⟩ := initialise s [] (by simpa using hz) hra hs (by intro i hi; simp at hi)
    obtain ⟨t,hu,hpc,ho⟩ := empty a 0 0 ha
    exact ⟨n+17,t,by omega,ht.append (trace_at_pc hp hu),hpc,by simpa only [RawPost,if_neg hb,if_pos hz] using ho⟩
  obtain ⟨hl,hmapped⟩ := hi (by omega) hz
  obtain ⟨n,t,hn,ht,hp,ho⟩ := decode_trace s bytes hl hra hm hmapped
  exact ⟨n,t,hn,ht,hp,by simpa only [RawPost,if_neg hb,if_neg hz] using ho⟩

theorem trace_returns {whole : Program} {entry : Word} {start n : Nat} {s t : State}
    (hi : Invocation program whole entry (s.getReg .x1) start s.memory) (hpc : s.pc = entry)
    (hn : n ≤ 256) (ht : Trace program 0 n (proofEntry s) t) (hret : t.pc = 0) :
    Returns whole (relocated program entry) (s.getReg .x1) 256 s
      ⟨relocateState program entry (s.getReg .x1) t,n⟩ := by
  have hentry := relocate_proofEntry program s entry rfl hpc
  have hleaf := ht.relocate leaf_layout hi.placement (proofEntry_ra s)
  rw [hentry] at hleaf
  have hwhole := hleaf.embed hi.slice hi.image.aligned hi.image.bounded
  have hfinish : (relocateState program entry (s.getReg .x1) t).pc = s.getReg .x1 := by
    simp [relocateState,hret,relocatePC]
  have hcallee := remap_callee (f := relocatePC (entry-program.base) (s.getReg .x1))
    (ra := s.getReg .x1) (callee_saved ht)
  change PreservesCallee (relocateState program entry (s.getReg .x1) (proofEntry s)) _ at hcallee
  rw [hentry] at hcallee
  exact ⟨hwhole.runUntil hfinish hi.image.valid 256 hn,hn,hfinish,
    by simp [relocateState],hcallee,
    fun k u hk hprefix => hleaf.embed_prefix_inCode hi.slice hi.image.aligned hi.image.bounded hk hprefix⟩

theorem remap_cleared {f : Word → Word} {ra : Word} {t : State} (h : Cleared t) :
    Cleared (remap f ra t) := by
  intro r hr h10 h11 h12
  have hne : r ≠ .x1 := by
    intro he; subst r; simp [Asm.Crypto.Sha2.cleared] at hr
  simpa only [remap_get _ _ _ _ hne] using h r hr h10 h11 h12

theorem remap_rawPost {f : Word → Word} {ra ptr len : Word} {bytes : List UInt8} {t : State}
    (h : RawPost ptr len bytes t) : RawPost ptr len bytes (remap f ra t) := by
  unfold RawPost at h ⊢
  split at h <;> simp only [*, ↓reduceIte]
  · exact ⟨by simpa [Output] using h.1,remap_cleared h.2⟩
  · split at h <;> simp only [*, ↓reduceIte]
    all_goals exact ⟨remap_decodePost h.1,remap_cleared h.2⟩

/-- All raw ABI branches in every admissible containing image and return address.
The input ownership is structural and conditional only on metadata validation. -/
theorem decode_embedded (whole : Program) (entry : Word) (start : Nat)
    (s : State) (bytes : List UInt8)
    (hi : Invocation program whole entry (s.getReg .x1) start s.memory) (hpc : s.pc = entry)
    (hbytes : InputAt s bytes) :
    ∃ done, Returns whole (relocated program entry) (s.getReg .x1) 256 s done ∧
      RawPost (s.getReg .x10) (s.getReg .x11) bytes done.state ∧
      done.state.memory = s.memory ∧ WriteTrace whole (s.getReg .x1) 0 0 done.steps s done.state := by
  obtain ⟨n,t,hn,ht,hret,hout⟩ := raw_trace (proofEntry s) bytes (proofEntry_ra s)
    (by simpa using hi.image.memory) (by simpa [InputAt] using hbytes)
  have htrace : Trace program 0 n (proofEntry s) t := by simpa only [proofEntry,atPC_atPC] using ht
  have hwrite := ((htrace.noStores no_stores 0 0).relocate leaf_layout hi.placement
    (proofEntry_ra s)).embed hi.slice hi.image.aligned hi.image.bounded
  rw [relocate_proofEntry program s entry rfl hpc] at hwrite
  refine ⟨⟨relocateState program entry (s.getReg .x1) t,n⟩,
    trace_returns hi hpc hn htrace hret,?_,?_,hwrite⟩
  · have hh := remap_rawPost (f := relocatePC (entry-program.base) (s.getReg .x1))
      (ra := s.getReg .x1) hout
    simpa only [relocateState,proofEntry_get _ _ (by decide : Reg.x10 ≠ .x1),
      proofEntry_get _ _ (by decide : Reg.x11 ≠ .x1)] using hh
  · simpa only [relocateState,remap_memory,proofEntry_memory] using htrace.memory_frame no_stores

end Libp2pAsm.Refinement.AsmProtobuf
