import Libp2pAsm.Refinement.AsmCodec.QuicDecode

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

set_option backward.isDefEq.respectTransparency false

theorem trace_at_pc {p stop n s t pc} (hpc : s.pc = pc)
    (h : Trace p stop n (atPC s pc) t) : Trace p stop n s t := by
  simpa only [← hpc, atPC_self] using h

theorem word_pred (n : Nat) (hn : 1 ≤ n) :
    BitVec.ofNat 64 n + (-1 : Word) = BitVec.ofNat 64 (n - 1) := by
  simpa only [Nat.sub_add_cancel hn] using word_succ_decrement (n - 1)

theorem quic_decode_body (s : State) (b : UInt8) (bs : List UInt8)
    (hb : s.getReg .x5 = BitVec.ofNat 64 b.toNat)
    (hw : s.getReg .x6 = BitVec.ofNat 64 (2^(b.toNat / 64)))
    (hcap : s.getReg .x6 ≤ s.getReg .x11) (hra : s.getReg .x1 = 0)
    (hr : Reads s.memory (s.getReg .x10) (b :: bs))
    (hfit : 2^(b.toNat / 64) - 1 ≤ bs.length) :
    ∃ t, Trace quicDecode 0 (9 + 7 * (2^(b.toNat / 64) - 1)) (atPC s 65576) t ∧
      t.pc = 0 ∧ Output 0
        (BitVec.ofNat 64 ((bs.take (2^(b.toNat / 64) - 1)).foldl
          (fun a b => a * 256 + b.toNat) (b.toNat % 64)))
        (BitVec.ofNat 64 (2^(b.toNat / 64))) t := by
  obtain ⟨wpos, wbound⟩ := quic_width_bound b
  obtain ⟨a, ha, hapc, hac, hav, hap, haw, ham⟩ := quic_decode_enter s b hb hcap
  have hlen : (bs.take (2^(b.toNat / 64) - 1)).length = 2^(b.toNat / 64) - 1 := by
    simp [List.length_take, Nat.min_eq_left hfit]
  have hread : Reads a.memory (a.getReg .x10) (bs.take (2^(b.toNat / 64) - 1)) := by
    rw [ham, hap]
    exact hr.tail.take _
  have hcount : a.getReg .x7 = BitVec.ofNat 64 (bs.take (2^(b.toNat / 64) - 1)).length := by
    rw [hac, hw, hlen, word_pred _ wpos]
  obtain ⟨u, hu, hupc, huv, huw⟩ := quic_tail_loop _ a (by rw [hlen]; omega) hcount hread
  have hau := ha.append (trace_at_pc hapc hu)
  have hura : u.getReg .x1 = 0 := by
    exact (codecs_return_address (.inr (.inl rfl)) hau).trans hra
  obtain ⟨t, ht, htpc, hout⟩ := quic_decode_finish u hura
  refine ⟨t, ?_, htpc, ?_⟩
  · have hn : 4 + (7 * (2^(b.toNat / 64) - 1) + 1) + 4 =
        9 + 7 * (2^(b.toNat / 64) - 1) := by omega
    simpa only [hlen, hn] using hau.append (trace_at_pc hupc ht)
  · simpa [huv, hav, huw, haw, hw, foldBytes_ofNat] using hout

/-- All QUIC byte strings, including empty/truncated and legal non-minimal inputs. -/
theorem quic_decode_trace (bytes : List UInt8) (s : State)
    (hl : bytes.length < 2^64) (hlen : s.getReg .x11 = BitVec.ofNat 64 bytes.length)
    (hra : s.getReg .x1 = 0) (hr : Reads s.memory (s.getReg .x10) bytes) :
    ∃ n t, n ≤ 64 ∧ Trace quicDecode 0 n (atPC s 65536) t ∧ t.pc = 0 ∧
      DecodePost (Spec.Codec.QuicVarint.decode bytes) t := by
  cases bytes with
  | nil =>
    obtain ⟨t, ht, hp, ho, _⟩ := quic_decode_empty_trace s hra (by simpa using hlen)
    exact ⟨5, t, by decide, ht, hp, ho⟩
  | cons b bs =>
    have hnonzero : s.getReg .x11 ≠ 0 := by
      rw [hlen]; exact word_length_nonzero _ hl (by simp)
    obtain ⟨a, ha, hapc, hab, haw, hap, hal, ham⟩ := quic_decode_header s b bs hnonzero hr
    have hara : a.getReg .x1 = 0 := (codecs_return_address (.inr (.inl rfl)) ha).trans hra
    have hread : Reads a.memory (a.getReg .x10) (b :: bs) := by simpa [ham, hap] using hr
    obtain ⟨wpos, wbound⟩ := quic_width_bound b
    have hlen64 : bs.length + 1 < 2^64 := hl
    by_cases hshort : bs.length < 2^(b.toNat / 64) - 1
    · have hlt : a.getReg .x11 < a.getReg .x6 := by
        rw [hal, hlen, haw]
        simp [BitVec.lt_def, Nat.mod_eq_of_lt hlen64]
        omega
      obtain ⟨t, ht, hp, ho⟩ := quic_decode_short a hara hlt
      refine ⟨10, t, by decide, ha.append (trace_at_pc hapc ht), hp, ?_⟩
      simpa [Spec.Codec.QuicVarint.decode_cons, hshort, DecodePost, errorCode] using ho
    · have hle : a.getReg .x6 ≤ a.getReg .x11 := by
        rw [haw, hal, hlen]
        simp [BitVec.le_def, Nat.mod_eq_of_lt hlen64]
        omega
      obtain ⟨t, ht, hp, ho⟩ := quic_decode_body a b bs hab haw hle hara hread (by omega)
      refine ⟨5 + (9 + 7 * (2^(b.toNat / 64) - 1)), t, by omega,
        ha.append (trace_at_pc hapc ht), hp, ?_⟩
      simpa [Spec.Codec.QuicVarint.decode_cons, hshort, DecodePost] using ho

end Libp2pAsm.Refinement.AsmCodec
