import Libp2pAsm.Refinement.AsmCodec.Relocation

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

/-- Derive all loads from owned bytes; no successful-load premise is required. -/
theorem invocation_reads (bytes padding : List UInt8) (base : Word)
    (w : Bool) (frame : List Region) (s : State)
    (hm : s.memory = heap base (bytes ++ padding).toArray w frame)
    (hb : base.toNat + (bytes ++ padding).length ≤ 2^64)
    (hptr : s.getReg .x10 = base) (hv : s.memory.valid = true) :
    Reads (proofEntry s).memory ((proofEntry s).getReg .x10) bytes := by
  simp only [proofEntry_memory, proofEntry_get _ _ (by decide : Reg.x10 ≠ .x1)]
  rw [hm, hptr]
  have hr := (heap_reads base (bytes ++ padding) w frame (by simpa [hm] using hv) hb).take bytes.length
  simpa using hr

/-- Universal QUIC decode, relocated and embedded, with the actual caller's ra. -/
theorem quic_decode_embedded (whole : Program) (entry : Word) (start : Nat)
    (bytes padding : List UInt8) (base : Word) (w : Bool) (frame : List Region) (s : State)
    (hi : Invocation quicDecode whole entry (s.getReg .x1) start s.memory)
    (hm : s.memory = heap base (bytes ++ padding).toArray w frame)
    (hb : base.toNat + (bytes ++ padding).length ≤ 2^64) (hl : bytes.length < 2^64)
    (hpc : s.pc = entry) (hptr : s.getReg .x10 = base)
    (hlen : s.getReg .x11 = BitVec.ofNat 64 bytes.length) :
    ∃ done, Returns whole (relocated quicDecode entry) (s.getReg .x1) 64 s done ∧
      DecodePost (Spec.Codec.QuicVarint.decode bytes) done.state ∧ done.state.memory = s.memory := by
  have hr := invocation_reads bytes padding base w frame s hm hb hptr hi.image.memory
  obtain ⟨n, t, hn, ht, hp, hout⟩ := quic_decode_trace bytes (proofEntry s) hl
    (by simpa using hlen) (proofEntry_ra s) hr
  have htrace : Trace quicDecode 0 n (proofEntry s) t := by
    simpa only [proofEntry, atPC_atPC] using ht
  refine ⟨⟨relocateState quicDecode entry (s.getReg .x1) t, n⟩,
    invocation_returns (.inr (.inl rfl)) hi hpc hn htrace hp, remap_decodePost hout, ?_⟩
  simpa only [relocateState, remap_memory, proofEntry_memory] using
    decoders_memory_frame (.inl rfl) htrace

/-- Universal unsigned decode, including truncation, overflow and nonminimal input. -/
theorem unsigned_decode_embedded (whole : Program) (entry : Word) (start : Nat)
    (bytes padding : List UInt8) (base : Word) (w : Bool) (frame : List Region) (s : State)
    (hi : Invocation unsignedDecode whole entry (s.getReg .x1) start s.memory)
    (hm : s.memory = heap base (bytes ++ padding).toArray w frame)
    (hb : base.toNat + (bytes ++ padding).length ≤ 2^64) (hl : bytes.length < 2^64)
    (hpc : s.pc = entry) (hptr : s.getReg .x10 = base)
    (hlen : s.getReg .x11 = BitVec.ofNat 64 bytes.length) :
    ∃ done, Returns whole (relocated unsignedDecode entry) (s.getReg .x1) 128 s done ∧
      DecodePost (Spec.Codec.UnsignedVarint.decode bytes) done.state ∧ done.state.memory = s.memory := by
  have hr := invocation_reads bytes padding base w frame s hm hb hptr hi.image.memory
  obtain ⟨n, t, hn, ht, hp, hout⟩ := unsigned_decode_trace bytes (proofEntry s) hl
    (by simpa using hlen) (proofEntry_ra s) hr
  have htrace : Trace unsignedDecode 0 n (proofEntry s) t := by
    simpa only [proofEntry, atPC_atPC] using ht
  refine ⟨⟨relocateState unsignedDecode entry (s.getReg .x1) t, n⟩,
    invocation_returns (.inr (.inr (.inr rfl))) hi hpc hn htrace hp, remap_decodePost hout, ?_⟩
  simpa only [relocateState, remap_memory, proofEntry_memory] using
    decoders_memory_frame (.inr rfl) htrace

end Libp2pAsm.Refinement.AsmCodec
