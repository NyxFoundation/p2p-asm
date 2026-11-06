import Libp2pAsm.Refinement.AsmCodec.Relocation

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

/-- Universal QUIC encode with a caller-selected image, entry and return address.
The exact write interval is empty on every error, proving failure atomicity. -/
theorem quic_encode_embedded (whole : Program) (entry : Word) (start : Nat)
    (s : State) (base : Word) (bytes : Array UInt8) (frame : List Region)
    (hi : Invocation quicEncode whole entry (s.getReg .x1) start s.memory)
    (hpc : s.pc = entry) (hp : s.getReg .x11 = base)
    (hm : s.memory = heap base bytes true frame) (hb : base.toNat + bytes.size ≤ 2^64)
    (hcap : (s.getReg .x12).toNat ≤ bytes.size) :
    ∃ done, Returns whole (relocated quicEncode entry) (s.getReg .x1) 128 s done ∧
      EncodePost (Spec.Codec.QuicVarint.encode (s.getReg .x10).toNat)
        (s.getReg .x12).toNat base bytes frame done.state ∧
      WriteTrace whole (s.getReg .x1) base.toNat
        (base.toNat + (encodeOutcome (Spec.Codec.QuicVarint.encode (s.getReg .x10).toNat)
          (s.getReg .x12).toNat).2.length) done.steps s done.state := by
  obtain ⟨n, t, hn, ht, hret, hout⟩ := quic_encode_trace (proofEntry s) base bytes frame
    (by simpa using hp) (by simpa using hm) hb (by simpa using hcap)
    (by simpa using hi.image.memory) (proofEntry_ra s)
  simp only [proofEntry_get _ _ (by decide : Reg.x10 ≠ .x1),
    proofEntry_get _ _ (by decide : Reg.x12 ≠ .x1)] at ht hout
  have htrace := writeTrace_at_pc (s := proofEntry s) rfl ht
  exact ⟨⟨relocateState quicEncode entry (s.getReg .x1) t, n⟩,
    invocation_returns (.inl rfl) hi hpc hn htrace.trace hret,
    remap_encodePost hout, invocation_writes (.inl rfl) hi hpc htrace⟩

/-- Universal unsigned encode; the existing arithmetic proof supplies all outcomes. -/
theorem unsigned_encode_embedded (whole : Program) (entry : Word) (start : Nat)
    (s : State) (base : Word) (bytes : Array UInt8) (frame : List Region)
    (hi : Invocation unsignedEncode whole entry (s.getReg .x1) start s.memory)
    (hpc : s.pc = entry) (hp : s.getReg .x11 = base)
    (hm : s.memory = heap base bytes true frame) (hb : base.toNat + bytes.size ≤ 2^64)
    (hcap : (s.getReg .x12).toNat ≤ bytes.size) :
    ∃ done, Returns whole (relocated unsignedEncode entry) (s.getReg .x1) 160 s done ∧
      EncodePost (Spec.Codec.UnsignedVarint.encode (s.getReg .x10).toNat)
        (s.getReg .x12).toNat base bytes frame done.state ∧
      WriteTrace whole (s.getReg .x1) base.toNat
        (base.toNat + (encodeOutcome (Spec.Codec.UnsignedVarint.encode (s.getReg .x10).toNat)
          (s.getReg .x12).toNat).2.length) done.steps s done.state := by
  obtain ⟨n, t, hn, ht, hret, hout⟩ := unsigned_encode_trace (proofEntry s) base bytes frame
    (by simpa using hp) (by simpa using hm) hb (by simpa using hcap)
    (by simpa using hi.image.memory) (proofEntry_ra s)
  simp only [proofEntry_get _ _ (by decide : Reg.x10 ≠ .x1),
    proofEntry_get _ _ (by decide : Reg.x12 ≠ .x1)] at ht hout
  have htrace := writeTrace_at_pc (s := proofEntry s) rfl ht
  exact ⟨⟨relocateState unsignedEncode entry (s.getReg .x1) t, n⟩,
    invocation_returns (.inr (.inr (.inl rfl))) hi hpc hn htrace.trace hret,
    remap_encodePost hout, invocation_writes (.inr (.inr (.inl rfl))) hi hpc htrace⟩

end Libp2pAsm.Refinement.AsmCodec
