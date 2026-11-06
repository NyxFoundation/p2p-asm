import Libp2pAsm.Refinement.AsmProtobuf.Blocks

namespace Libp2pAsm.Refinement.AsmProtobuf
open Rv64 Rv64.Logic AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

/-- All ten byte positions, including overflow before accumulation at position ten. -/
theorem scan (fuel : Nat) (s : State) (bytes : List UInt8) (acc count : Nat)
    (hf : 0 < fuel) (hc : count+fuel = 10) (ha : acc < 2^(7*count))
    (hl : bytes.length < 2^64) (hi : Inv s bytes acc count) :
    ∃ n t, n ≤ 17*fuel+17 ∧ Trace program 0 n (atPC s 65640) t ∧ t.pc = 0 ∧
      Post (Spec.Codec.ProtobufVarint.decodeLoop fuel count acc bytes) t := by
  induction fuel generalizing s bytes acc count with
  | zero => omega
  | succ fuel ih =>
    cases bytes with
    | nil =>
      obtain ⟨t, ht, hp, ho⟩ := empty s acc count hi
      exact ⟨17, t, by omega, ht, hp, ho⟩
    | cons b bs =>
      by_cases hg : count = 9 ∧ 1 < b.toNat
      · obtain ⟨rfl, hb⟩ := hg
        obtain ⟨t, ht, hp, ho⟩ := overflow s b bs acc hl hb hi
        exact ⟨22, t, by omega, ht, hp, by simpa [Spec.Codec.ProtobufVarint.decodeLoop, hb] using ho⟩
      have guard : count = 9 → b.toNat ≤ 1 := by omega
      obtain ⟨nr, r, hnr, hr, hpc, hri⟩ := read s b bs acc count (by omega) ha hl guard hi
      by_cases hb : b.toNat < 128
      · obtain ⟨t, ht, hp, ho⟩ := terminal r b bs acc count hb hri
        exact ⟨nr+17, t, by omega, hr.append (trace_at_pc hpc ht), hp,
          by simpa [Spec.Codec.ProtobufVarint.decodeLoop, Bool.and_eq_true, hg, hb] using ho⟩
      · have hcount : count < 9 := by have := guard; omega
        obtain ⟨u, hu, hupc, hui⟩ := continuation r b bs acc count hb hri
        obtain ⟨n, t, hn, ht, hp, ho⟩ := ih u bs (acc+b.toNat%128*2^(7*count))
          (count+1) (by omega) (by omega) (unsigned_accumulate_bound acc count b ha)
          (by simp_all; omega) hui
        exact ⟨nr+5+n, t, by omega,
          (hr.append (trace_at_pc hpc hu)).append (trace_at_pc hupc ht), hp,
          by simpa [Spec.Codec.ProtobufVarint.decodeLoop, show count ≠ 9 by omega, hb] using ho⟩

theorem initialise (s : State) (bytes : List UInt8)
    (hlen : s.getReg .x11 = BitVec.ofNat 64 bytes.length) (hra : s.getReg .x1 = 0)
    (hspan : (s.getReg .x10).toNat+(s.getReg .x11).toNat ≤ 2^64)
    (hr : Reads s.memory (s.getReg .x10) bytes) :
    ∃ n t, n ≤ 10 ∧ Trace program 0 n (atPC s 65536) t ∧ t.pc = 65640 ∧
      Inv t bytes 0 0 := by
  by_cases hz : s.getReg .x11 = 0
  · refine ⟨4, ?_, by decide, ?trace, ?post⟩
    case trace =>
      repeat parser_step
      exact .nil _
    case post => simp_all [Inv, getReg_setReg]
  · have hg := (Parser.range_iff (s.getReg .x10) (s.getReg .x11) hz).mpr hspan
    change s.getReg .x11+18446744073709551615 ≤ (18446744073709551615 : Word)-s.getReg .x10 at hg
    refine ⟨9, ?_, by decide, ?trace, ?post⟩
    case trace =>
      repeat parser_step
      exact .nil _
    case post => simp_all [Inv, getReg_setReg]

theorem range_return (s : State) (hra : s.getReg .x1 = 0) :
    ∃ t, Trace program 0 16 (atPC s 65556) t ∧ t.pc = 0 ∧ Output 4 0 0 t ∧ Cleared t := by
  refine ⟨?_, ?trace, ?post⟩
  case trace =>
    repeat parser_step
    exact .nil _
  case post => simp [Output, Cleared, Asm.Crypto.Sha2.cleared, getReg_setReg]

theorem range_error (s : State) (hra : s.getReg .x1 = 0)
    (hb : 2^64 < (s.getReg .x10).toNat+(s.getReg .x11).toNat) :
    ∃ t, Trace program 0 21 (atPC s 65536) t ∧ t.pc = 0 ∧ Output 4 0 0 t ∧ Cleared t := by
  have hn : s.getReg .x11 ≠ 0 := by
    intro hz; have := (s.getReg .x10).isLt; simp [hz] at hb; omega
  have hg : ¬s.getReg .x11+(-1 : Word) ≤ (-1 : Word)-s.getReg .x10 := by
    rw [Parser.range_iff _ _ hn]; omega
  change ¬s.getReg .x11+18446744073709551615 ≤ (18446744073709551615 : Word)-s.getReg .x10 at hg
  simp only [BitVec.ofNat_eq_ofNat] at *
  have hprefix : ∃ a, Trace program 0 5 (atPC s 65536) a ∧ a.pc = 65556 ∧ a.getReg .x1 = 0 := by
    refine ⟨?_, ?trace, ?post⟩
    case trace =>
      repeat parser_step
      exact .nil _
    case post => simp [getReg_setReg, hra]
  obtain ⟨a,ht,hp,hr⟩ := hprefix
  obtain ⟨t,hu,hpc,ho⟩ := range_return a hr
  exact ⟨t,ht.append (trace_at_pc hp hu),hpc,ho⟩

/-- Total execution from structural byte ownership; no successful outcome is assumed. -/
theorem decode_trace (s : State) (bytes : List UInt8)
    (hlen : (s.getReg .x11).toNat = bytes.length) (hra : s.getReg .x1 = 0)
    (hm : s.memory.valid = true) (hbytes : Parser.BytesAt s.memory (s.getReg .x10) bytes) :
    ∃ n t, n ≤ 256 ∧ Trace program 0 n (atPC s 65536) t ∧ t.pc = 0 ∧
      Post (Spec.Codec.ProtobufVarint.decode bytes) t := by
  have hl : bytes.length < 2^64 := by rw [← hlen]; exact (s.getReg .x11).isLt
  have hword : s.getReg .x11 = BitVec.ofNat 64 bytes.length := by rw [← hlen]; simp
  have hspan : (s.getReg .x10).toNat+(s.getReg .x11).toNat ≤ 2^64 := by
    simpa [hlen] using hbytes.nonwrap
  obtain ⟨ni, i, hni, hi, hipc, hii⟩ := initialise s bytes hword hra hspan (hbytes.reads hm)
  obtain ⟨n, t, hn, ht, hp, ho⟩ := scan 10 i bytes 0 0 (by decide) rfl (by decide) hl hii
  exact ⟨ni+n, t, by omega, hi.append (trace_at_pc hipc ht), hp, ho⟩

end Libp2pAsm.Refinement.AsmProtobuf
