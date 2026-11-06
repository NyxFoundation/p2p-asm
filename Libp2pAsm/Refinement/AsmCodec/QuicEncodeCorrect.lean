import Libp2pAsm.Refinement.AsmCodec.QuicEncodeBlocks
import Libp2pAsm.Refinement.AsmCodec.QuicSelect
import Libp2pAsm.Refinement.AsmCodec.EncodeContract

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

theorem quic_encode_trace (s : State) (base : Word) (bytes : Array UInt8) (frame : List Region)
    (hp : s.getReg .x11 = base) (hm : s.memory = heap base bytes true frame)
    (hb : base.toNat + bytes.size ≤ 2^64) (hcap : (s.getReg .x12).toNat ≤ bytes.size)
    (hv : s.memory.valid = true) (hra : s.getReg .x1 = 0) :
    ∃ n t, n ≤ 128 ∧ WriteTrace quicEncode 0 base.toNat (base.toNat + (encodeOutcome (Spec.Codec.QuicVarint.encode (s.getReg .x10).toNat)
        (s.getReg .x12).toNat).2.length) n (atPC s 65536) t ∧ t.pc = 0 ∧
      EncodePost (Spec.Codec.QuicVarint.encode (s.getReg .x10).toNat)
        (s.getReg .x12).toNat base bytes frame t := by
  let lower := base.toNat
  let upper := base.toNat + (encodeOutcome (Spec.Codec.QuicVarint.encode (s.getReg .x10).toNat)
        (s.getReg .x12).toNat).2.length
  by_cases hfit : (s.getReg .x10).toNat < 2^62
  · obtain ⟨n, a, hn, ha, hapc, haw, hat, hav, hap, hac, ham⟩ := quic_select (lower := lower) (upper := upper) s hfit
    have hara : a.getReg .x1 = 0 := (codecs_return_address (.inl rfl) ha.trace).trans hra
    have hspec := quicOutput_spec (s.getReg .x10) hfit
    obtain ⟨wpos, wbound⟩ := quic_widthTag_bounds (s.getReg .x10).toNat
    let w := (Spec.Codec.QuicVarint.widthTag (s.getReg .x10).toNat).1
    have hw64 : w < 2^64 := by dsimp [w]; omega
    by_cases hshort : (s.getReg .x12).toNat < w
    · have hc : a.getReg .x12 < a.getReg .x5 := by
        rw [hac, haw]
        change (s.getReg .x12).toNat < w % 2^64
        simpa only [Nat.mod_eq_of_lt hw64] using hshort
      obtain ⟨t, ht, htpc, hout, htm⟩ := quic_encode_short (lower := lower) (upper := upper) a hara hc
      refine ⟨n+5, t, by omega, ha.append (writeTrace_at_pc hapc ht), htpc, ?_⟩
      have hnot : ¬w ≤ (s.getReg .x12).toNat := by omega
      simpa [EncodePost, encodeOutcome, hspec, quicOutput_length, hnot, w, patchBytes,
        htm, ham, hm] using hout
    · have hle : w ≤ (s.getReg .x12).toNat := by omega
      have hc : a.getReg .x5 ≤ a.getReg .x12 := by
        rw [haw, hac]
        change w % 2^64 ≤ (s.getReg .x12).toNat
        rw [Nat.mod_eq_of_lt hw64]
        omega
      obtain ⟨b, he, hbpc, hbi, hbw⟩ := quic_encode_enter (lower := lower) (upper := upper) a w base bytes frame wpos haw hc
        (hap.trans hp) (ham.trans hm)
      obtain ⟨u, hu, hupc, hum, huw⟩ := quic_emit_loop (lower := lower) (upper := upper) w b (a.getReg .x10)
        (BitVec.ofNat 64 (8*(w-1))) (a.getReg .x7) base 0 bytes frame wbound
        (by omega) hb (by simpa [hm] using hv) hbi (by simp [lower])
        (by simp [upper, hspec, encodeOutcome, quicOutput_length, hle, w])
      have hprefix := (ha.append (writeTrace_at_pc hapc he)).append (writeTrace_at_pc hbpc hu)
      have hura : u.getReg .x1 = 0 := (codecs_return_address (.inl rfl) hprefix.trace).trans hra
      obtain ⟨t, ht, htpc, hout, htm⟩ := quic_encode_finish (lower := lower) (upper := upper) u hura
      refine ⟨n+4+(10*w+1)+4, t, by dsimp [w] at *; omega,
        hprefix.append (writeTrace_at_pc hupc ht), htpc, ?_⟩
      have hle : w ≤ (s.getReg .x12).toNat := by omega
      have ho : Output 0 (BitVec.ofNat 64 w) 0 t := by simpa [huw, hbw] using hout
      have hmemory := htm.trans hum
      simpa [EncodePost, encodeOutcome, hspec, quicOutput_length, hle, w,
        hav, hat] using And.intro ho hmemory
  · obtain ⟨t, ht, htpc, hout, htm⟩ := quic_encode_overflow_trace (lower := lower) (upper := upper) s hra
      (word_shift_nonzero _ 62 (by omega))
    refine ⟨6, t, by decide, ht, htpc, ?_⟩
    have hspec := Spec.Codec.QuicVarint.encode_overflow (s.getReg .x10).toNat (by omega)
    simpa [EncodePost, encodeOutcome, hspec, errorCode, patchBytes, htm, hm] using hout

/-- Universal encoder result, capacity handling, exact byte writes, and ABI preservation. -/
theorem quic_encode_runUntil (s : State) (base : Word) (bytes : Array UInt8) (frame : List Region)
    (hpc : s.pc = 65536) (hp : s.getReg .x11 = base) (hm : s.memory = heap base bytes true frame)
    (hb : base.toNat + bytes.size ≤ 2^64) (hcap : (s.getReg .x12).toNat ≤ bytes.size)
    (hv : quicEncode.valid s.memory = true) (hra : s.getReg .x1 = 0) :
    ∃ done, runUntil quicEncode 0 128 s = .ok done ∧ done.steps ≤ 128 ∧ done.state.pc = 0 ∧
      EncodePost (Spec.Codec.QuicVarint.encode (s.getReg .x10).toNat)
        (s.getReg .x12).toNat base bytes frame done.state ∧ PreservesCallee s done.state ∧
      WriteTrace quicEncode 0 base.toNat (base.toNat + (encodeOutcome (Spec.Codec.QuicVarint.encode (s.getReg .x10).toNat)
        (s.getReg .x12).toNat).2.length)
        done.steps s done.state := by
  have hmv : s.memory.valid = true := by
    simp only [Program.valid, Bool.and_eq_true] at hv; exact hv.1.1
  obtain ⟨n, t, hn, ht, htpc, hout⟩ := quic_encode_trace s base bytes frame hp hm hb hcap hmv hra
  have he := writeTrace_at_pc hpc ht
  exact ⟨⟨t, n⟩, he.trace.runUntil htpc hv 128 hn, hn, htpc, hout, codecs_callee_saved (.inl rfl) he.trace, he⟩

end Libp2pAsm.Refinement.AsmCodec
