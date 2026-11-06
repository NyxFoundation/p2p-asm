import Libp2pAsm.Rv64.Logic.WriteTrace
import Libp2pAsm.Refinement.AsmCodec.QuicEmit
import Libp2pAsm.Refinement.AsmCodec.QuicCorrect

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

variable {lower upper : Nat}

set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false

theorem quic_encode_short (s : State) (hra : s.getReg .x1 = 0)
    (hc : s.getReg .x12 < s.getReg .x5) :
    ∃ t, WriteTrace quicEncode 0 lower upper 5 (atPC s 65632) t ∧ t.pc = 0 ∧ Output 1 0 0 t ∧
      t.memory = s.memory := by
  have hn : ¬s.getReg .x5 ≤ s.getReg .x12 := BitVec.not_le.mpr hc
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    write_step (.BGEU .x12 .x5 24)
    write_step (.ADDI .x10 .x0 1)
    write_step (.ADDI .x11 .x0 0)
    write_step (.ADDI .x12 .x0 0)
    write_step (.JALR .x0 .x1 0)
    exact .nil _
  case post => simp [Output, getReg_setReg]

theorem quic_initial_shift (w : Nat) (hw : 1 ≤ w) :
    (BitVec.ofNat 64 w + 18446744073709551615#64) <<< (3 : Nat) =
      BitVec.ofNat 64 (8*(w-1)) := by
  have he := word_pred w hw
  change (BitVec.ofNat 64 w + (-1 : Word)) <<< (3 : Nat) = _
  rw [he]
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftLeft_eq, Nat.mul_mod, Nat.mul_comm]

theorem quic_encode_enter (s : State) (w : Nat) (base : Word) (bytes : Array UInt8) (frame : List Region)
    (hw : 1 ≤ w) (hwidth : s.getReg .x5 = BitVec.ofNat 64 w)
    (hc : s.getReg .x5 ≤ s.getReg .x12) (hp : s.getReg .x11 = base)
    (hm : s.memory = heap base bytes true frame) :
    ∃ t, WriteTrace quicEncode 0 lower upper 4 (atPC s 65632) t ∧ t.pc = 65668 ∧
      QuicEmitInv t (s.getReg .x10) (BitVec.ofNat 64 (8*(w-1))) (s.getReg .x7) w base 0 bytes frame ∧
      t.getReg .x31 = BitVec.ofNat 64 w := by
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    write_step (.BGEU .x12 .x5 24)
    write_step_plain (.ADDI .x31 .x5 0)
    write_step_plain (.ADDI .x6 .x5 (-1))
    write_step_plain (.SLLI .x6 .x6 3)
    exact .nil _
  case post =>
    simp [QuicEmitInv, getReg_setReg, hp, hm]
    refine ⟨⟨hwidth, ?_⟩, hwidth⟩
    rw [hwidth]
    simpa using quic_initial_shift w hw

theorem quic_encode_finish (s : State) (hra : s.getReg .x1 = 0) :
    ∃ t, WriteTrace quicEncode 0 lower upper 4 (atPC s 65708) t ∧ t.pc = 0 ∧
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
