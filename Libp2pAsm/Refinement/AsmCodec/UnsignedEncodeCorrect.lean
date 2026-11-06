import Libp2pAsm.Refinement.AsmCodec.UnsignedEncodeBlocks

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

theorem unsigned_encode_trace (s : State) (base : Word) (bytes : Array UInt8) (frame : List Region)
    (hp : s.getReg .x11 = base) (hm : s.memory = heap base bytes true frame)
    (hb : base.toNat + bytes.size ≤ 2^64) (hcap : (s.getReg .x12).toNat ≤ bytes.size)
    (hv : s.memory.valid = true) (hra : s.getReg .x1 = 0) :
    ∃ n t, n ≤ 160 ∧ WriteTrace unsignedEncode 0 base.toNat (base.toNat + (encodeOutcome (Spec.Codec.UnsignedVarint.encode (s.getReg .x10).toNat)
        (s.getReg .x12).toNat).2.length) n (atPC s 65536) t ∧ t.pc = 0 ∧
      EncodePost (Spec.Codec.UnsignedVarint.encode (s.getReg .x10).toNat)
        (s.getReg .x12).toNat base bytes frame t := by
  let lower := base.toNat
  let upper := base.toNat + (encodeOutcome (Spec.Codec.UnsignedVarint.encode (s.getReg .x10).toNat)
        (s.getReg .x12).toNat).2.length
  by_cases hfit : (s.getReg .x10).toNat < 2^63
  · obtain ⟨encoded, n, a, hspec, hpos, hlen, hn, ha, hapc, haw31, haw6, hav, hap, hac, ham⟩ :=
      unsigned_select (lower := lower) (upper := upper) s hfit
    have hara : a.getReg .x1 = 0 := (codecs_return_address (.inr (.inr (.inl rfl))) ha.trace).trans hra
    have hw64 : encoded.length < 2^64 := by omega
    by_cases hshort : (s.getReg .x12).toNat < encoded.length
    · have hc : a.getReg .x12 < a.getReg .x6 := by
        rw [hac, haw6]
        change (s.getReg .x12).toNat < encoded.length % 2^64
        simpa only [Nat.mod_eq_of_lt hw64] using hshort
      obtain ⟨t, ht, htpc, hout, htm⟩ := unsigned_encode_short (lower := lower) (upper := upper) a hara hc
      refine ⟨n+5, t, by omega, ha.append (writeTrace_at_pc hapc ht), htpc, ?_⟩
      have hnot : ¬encoded.length ≤ (s.getReg .x12).toNat := by omega
      simpa [EncodePost, encodeOutcome, hspec, hnot, patchBytes, htm, ham, hm] using hout
    · have hle : encoded.length ≤ (s.getReg .x12).toNat := by omega
      have hc : a.getReg .x6 ≤ a.getReg .x12 := by
        rw [haw6, hac]
        change encoded.length % 2^64 ≤ (s.getReg .x12).toNat
        rw [Nat.mod_eq_of_lt hw64]; omega
      have hai : UnsignedEmitInv a (s.getReg .x10) encoded.length base 0 bytes frame := by
        exact ⟨hav, haw6, by simpa using hap.trans hp, ham.trans hm⟩
      obtain ⟨m, u, hmcount, hu, hupc, hum, huw⟩ := unsigned_emit_loop (lower := lower) (upper := upper) encoded.length a
        (s.getReg .x10) base 0 bytes frame hlen (by omega) hb (by simpa [hm] using hv) hai (by simp [lower])
        (by simp [upper, hspec, encodeOutcome, hle])
      have hprefix := (ha.append (writeTrace_at_pc hapc (unsigned_encode_enter (lower := lower) (upper := upper) a hc))).append hu
      have hura : u.getReg .x1 = 0 :=
        (codecs_return_address (.inr (.inr (.inl rfl))) hprefix.trace).trans hra
      obtain ⟨t, ht, htpc, hout, htm⟩ := unsigned_encode_finish (lower := lower) (upper := upper) u hura
      refine ⟨n+1+m+4, t, by omega, hprefix.append (writeTrace_at_pc hupc ht), htpc, ?_⟩
      have hle : encoded.length ≤ (s.getReg .x12).toNat := by omega
      have hloop : Spec.Codec.UnsignedVarint.encodeLoop 9 (s.getReg .x10).toNat = .ok encoded := by
        simpa [Spec.Codec.UnsignedVarint.encode, Nat.not_le_of_gt hfit] using hspec
      have he := unsignedOutput_spec 9 (s.getReg .x10) encoded hloop
      have ho : Output 0 (BitVec.ofNat 64 encoded.length) 0 t := by simpa [huw, haw31] using hout
      simpa [EncodePost, encodeOutcome, hspec, hle, he] using And.intro ho (htm.trans hum)
  · obtain ⟨t, ht, htpc, hout, htm⟩ := unsigned_encode_overflow_trace (lower := lower) (upper := upper) s hra
      (word_shift_nonzero _ 63 (by omega))
    refine ⟨6, t, by decide, ht, htpc, ?_⟩
    have hspec := Spec.Codec.UnsignedVarint.encode_overflow (s.getReg .x10).toNat (by omega)
    simpa [EncodePost, encodeOutcome, hspec, errorCode, patchBytes, htm, hm] using hout

theorem unsigned_encode_runUntil (s : State) (base : Word) (bytes : Array UInt8) (frame : List Region)
    (hpc : s.pc = 65536) (hp : s.getReg .x11 = base) (hm : s.memory = heap base bytes true frame)
    (hb : base.toNat + bytes.size ≤ 2^64) (hcap : (s.getReg .x12).toNat ≤ bytes.size)
    (hv : unsignedEncode.valid s.memory = true) (hra : s.getReg .x1 = 0) :
    ∃ done, runUntil unsignedEncode 0 160 s = .ok done ∧ done.steps ≤ 160 ∧ done.state.pc = 0 ∧
      EncodePost (Spec.Codec.UnsignedVarint.encode (s.getReg .x10).toNat)
        (s.getReg .x12).toNat base bytes frame done.state ∧ PreservesCallee s done.state ∧
      WriteTrace unsignedEncode 0 base.toNat (base.toNat + (encodeOutcome (Spec.Codec.UnsignedVarint.encode (s.getReg .x10).toNat)
        (s.getReg .x12).toNat).2.length)
        done.steps s done.state := by
  have hmv : s.memory.valid = true := by
    simp only [Program.valid, Bool.and_eq_true] at hv; exact hv.1.1
  obtain ⟨n, t, hn, ht, htpc, hout⟩ := unsigned_encode_trace s base bytes frame hp hm hb hcap hmv hra
  have he := writeTrace_at_pc hpc ht
  exact ⟨⟨t, n⟩, he.trace.runUntil htpc hv 160 hn, hn, htpc, hout,
    codecs_callee_saved (.inr (.inr (.inl rfl))) he.trace, he⟩

end Libp2pAsm.Refinement.AsmCodec
