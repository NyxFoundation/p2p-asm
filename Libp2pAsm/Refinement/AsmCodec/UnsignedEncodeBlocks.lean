import Libp2pAsm.Rv64.Logic.WriteTrace
import Libp2pAsm.Refinement.AsmCodec.UnsignedCount
import Libp2pAsm.Refinement.AsmCodec.UnsignedEmit

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

variable {lower upper : Nat}

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

theorem unsigned_encode_initialize (s : State) (hv : (s.getReg .x10).toNat < 2^63) :
    ∃ t, WriteTrace unsignedEncode 0 lower upper 5 (atPC s 65536) t ∧ t.pc = 65576 ∧
      CountInv t (s.getReg .x10).toNat 1 ∧ SameInputs s t := by
  have hz := (word_shift_zero_iff (s.getReg .x10) 63).2 hv
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    write_step (.SRLI .x5 .x10 63)
    write_step (.BEQ .x5 .x0 24)
    write_step (.ADDI .x5 .x10 0)
    write_step (.ADDI .x6 .x0 1)
    write_step (.ADDI .x7 .x0 128)
    exact .nil _
  case post => simp [CountInv, SameInputs, getReg_setReg]

theorem unsigned_copy_width (s : State) :
    ∃ t, WriteTrace unsignedEncode 0 lower upper 1 (atPC s 65592) t ∧ t.pc = 65596 ∧
      t.getReg .x31 = s.getReg .x6 ∧ t.getReg .x6 = s.getReg .x6 ∧ SameInputs s t := by
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    write_step_plain (.ADDI .x31 .x6 0)
    exact .nil _
  case post => simp [SameInputs, getReg_setReg]

theorem unsigned_select (s : State) (hv : (s.getReg .x10).toNat < 2^63) :
    ∃ encoded n t, Spec.Codec.UnsignedVarint.encode (s.getReg .x10).toNat = .ok encoded ∧
      0 < encoded.length ∧ encoded.length ≤ 9 ∧ n ≤ 42 ∧
      WriteTrace unsignedEncode 0 lower upper n (atPC s 65536) t ∧ t.pc = 65596 ∧
      t.getReg .x31 = BitVec.ofNat 64 encoded.length ∧
      t.getReg .x6 = BitVec.ofNat 64 encoded.length ∧ SameInputs s t := by
  obtain ⟨a, ha, hapc, hai, has⟩ := unsigned_encode_initialize (lower := lower) (upper := upper) s hv
  obtain ⟨encoded, n, b, he, hpos, hlen, hn, hb, hbpc, hbw, hbs⟩ :=
    unsigned_count_loop (lower := lower) (upper := upper) 9 a (s.getReg .x10).toNat 1 (by decide) (by decide) hv hai
  obtain ⟨t, ht, htpc, hw31, hw6, hs⟩ := unsigned_copy_width (lower := lower) (upper := upper) b
  refine ⟨encoded, 5+n+1, t, ?_, hpos, hlen, by omega,
    (ha.append (writeTrace_at_pc hapc hb)).append (writeTrace_at_pc hbpc ht), htpc, ?_, ?_,
    (has.trans hbs).trans hs⟩
  · simp [Spec.Codec.UnsignedVarint.encode, Nat.not_le_of_gt hv, he]
  · simpa [hbw, Nat.add_comm] using hw31
  · simpa [hbw, Nat.add_comm] using hw6

theorem unsigned_encode_short (s : State) (hra : s.getReg .x1 = 0)
    (hc : s.getReg .x12 < s.getReg .x6) :
    ∃ t, WriteTrace unsignedEncode 0 lower upper 5 (atPC s 65596) t ∧ t.pc = 0 ∧ Output 1 0 0 t ∧
      t.memory = s.memory := by
  have hn : ¬s.getReg .x6 ≤ s.getReg .x12 := BitVec.not_le.mpr hc
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    write_step (.BGEU .x12 .x6 24)
    write_step (.ADDI .x10 .x0 1)
    write_step (.ADDI .x11 .x0 0)
    write_step (.ADDI .x12 .x0 0)
    write_step (.JALR .x0 .x1 0)
    exact .nil _
  case post => simp [Output, getReg_setReg]

theorem unsigned_encode_enter (s : State) (hc : s.getReg .x6 ≤ s.getReg .x12) :
    WriteTrace unsignedEncode 0 lower upper 1 (atPC s 65596) (atPC s 65620) := by
  write_step (.BGEU .x12 .x6 24)
  exact .nil _

theorem unsigned_encode_finish (s : State) (hra : s.getReg .x1 = 0) :
    ∃ t, WriteTrace unsignedEncode 0 lower upper 4 (atPC s 65660) t ∧ t.pc = 0 ∧
      Output 0 (s.getReg .x31) 0 t ∧ t.memory = s.memory := by
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    write_step (.ADDI .x11 .x31 0)
    write_step (.ADDI .x12 .x0 0)
    write_step (.ADDI .x10 .x0 0)
    write_step (.JALR .x0 .x1 0)
    exact .nil _
  case post => simp [Output, getReg_setReg]

end Libp2pAsm.Refinement.AsmCodec
