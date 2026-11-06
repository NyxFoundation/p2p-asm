import Libp2pAsm.Refinement.AsmCodec.UnsignedBranches

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

theorem unsigned_terminal (s : State) (b : UInt8) (bs : List UInt8) (acc count fuel : Nat)
    (hc : count < 9) (hb : b.toNat < 128) (hi : UnsignedReadInv s (b :: bs) acc count b) :
    ∃ n t, n ≤ 8 ∧ Trace unsignedDecode 0 n (atPC s 65580) t ∧ t.pc = 0 ∧
      DecodePost (Spec.Codec.UnsignedVarint.decodeLoop (fuel+1) (b :: bs) acc (7*count) count) t := by
  by_cases hz : count = 0
  · subst count
    obtain ⟨t, ht, hp, ho⟩ := unsigned_terminal_first s b bs acc hb hi
    refine ⟨7, t, by decide, ht, hp, ?_⟩
    simpa [Spec.Codec.UnsignedVarint.decodeLoop, hb, DecodePost] using ho
  · have hcpos : 0 < count := by omega
    obtain ⟨t, ht, hp, ho⟩ := unsigned_terminal_long s b bs acc count hcpos hc hb hi
    refine ⟨8, t, by decide, ht, hp, ?_⟩
    by_cases hpay : b.toNat % 128 = 0 <;>
      simpa [Spec.Codec.UnsignedVarint.decodeLoop, hb, hcpos, hpay, DecodePost, errorCode] using ho

/-- Nine-byte scan: all terminal, truncated, non-minimal, and overflow paths. -/
theorem unsigned_scan (fuel : Nat) (s : State) (bytes : List UInt8) (acc count : Nat)
    (hf : 0 < fuel) (hc : count + fuel = 9) (ha : acc < 2^(7*count))
    (hl : bytes.length < 2^64) (hi : UnsignedInv s bytes acc count) :
    ∃ n t, n ≤ 13*fuel+2 ∧ Trace unsignedDecode 0 n (atPC s 65552) t ∧ t.pc = 0 ∧
      DecodePost (Spec.Codec.UnsignedVarint.decodeLoop fuel bytes acc (7*count) count) t := by
  induction fuel generalizing s bytes acc count with
  | zero => omega
  | succ fuel ih =>
    cases bytes with
    | nil =>
      obtain ⟨t, ht, hp, ho⟩ := unsigned_empty s acc count hi
      exact ⟨5, t, by omega, ht, hp, ho⟩
    | cons b bs =>
      obtain ⟨a, ht, hpc, hri⟩ := unsigned_read s b bs acc count (by omega) ha hl hi
      by_cases hb : b.toNat < 128
      · obtain ⟨n, t, hn, hu, hp, ho⟩ := unsigned_terminal a b bs acc count fuel (by omega) hb hri
        exact ⟨7+n, t, by omega, ht.append (trace_at_pc hpc hu), hp, ho⟩
      · by_cases hz : fuel = 0
        · subst fuel
          have hc8 : count = 8 := by omega
          subst count
          obtain ⟨t, hu, hp, ho⟩ := unsigned_overflow a b bs acc hb hri
          refine ⟨13, t, by decide, ht.append (trace_at_pc hpc hu), hp, ?_⟩
          simpa [Spec.Codec.UnsignedVarint.decodeLoop, hb, DecodePost, errorCode] using ho
        · obtain ⟨u, hu, hupc, hui⟩ := unsigned_continue a b bs acc count (by omega) hb hri
          obtain ⟨n, t, hn, hv, hp, ho⟩ := ih u bs
            (acc + b.toNat % 128 * 2^(7*count)) (count+1) (by omega) (by omega)
            (unsigned_accumulate_bound acc count b ha) (by simp_all; omega) hui
          refine ⟨7+6+n, t, by omega,
            (ht.append (trace_at_pc hpc hu)).append (trace_at_pc hupc hv), hp, ?_⟩
          simpa [Spec.Codec.UnsignedVarint.decodeLoop, hb, Nat.mul_add] using ho

/-- Total universal unsigned decoder correspondence, with a 128-instruction budget. -/
theorem unsigned_decode_trace (bytes : List UInt8) (s : State)
    (hl : bytes.length < 2^64) (hlen : s.getReg .x11 = BitVec.ofNat 64 bytes.length)
    (hra : s.getReg .x1 = 0) (hr : Reads s.memory (s.getReg .x10) bytes) :
    ∃ n t, n ≤ 128 ∧ Trace unsignedDecode 0 n (atPC s 65536) t ∧ t.pc = 0 ∧
      DecodePost (Spec.Codec.UnsignedVarint.decode bytes) t := by
  obtain ⟨a, ha, hapc, hi⟩ := unsigned_initialize s bytes hlen hra hr
  obtain ⟨n, t, hn, ht, hp, ho⟩ := unsigned_scan 9 a bytes 0 0 (by decide) rfl (by decide) hl hi
  exact ⟨4+n, t, by omega, ha.append (trace_at_pc hapc ht), hp, ho⟩

end Libp2pAsm.Refinement.AsmCodec
