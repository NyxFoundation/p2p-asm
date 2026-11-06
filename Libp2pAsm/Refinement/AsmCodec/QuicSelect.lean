import Libp2pAsm.Refinement.AsmCodec.Programs
import Libp2pAsm.Refinement.AsmCodec.EncodeArithmetic
import Libp2pAsm.Rv64.Logic.WriteTrace

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

variable {lower upper : Nat}

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000

def QuicSelected (s t : State) : Prop :=
  t.getReg .x5 = BitVec.ofNat 64 (Spec.Codec.QuicVarint.widthTag (s.getReg .x10).toNat).1 ∧
  t.getReg .x7 = BitVec.ofNat 64 (Spec.Codec.QuicVarint.widthTag (s.getReg .x10).toNat).2 ∧
  t.getReg .x10 = s.getReg .x10 ∧ t.getReg .x11 = s.getReg .x11 ∧
  t.getReg .x12 = s.getReg .x12 ∧ t.memory = s.memory

/-- Width selection follows the existing branch layout and handles every fitting word. -/
theorem quic_select (s : State) (hv : (s.getReg .x10).toNat < 2^62) :
    ∃ n t, n ≤ 11 ∧ WriteTrace quicEncode 0 lower upper n (atPC s 65536) t ∧ t.pc = 65632 ∧ QuicSelected s t := by
  have htop := (word_shift_zero_iff (s.getReg .x10) 62).2 hv
  by_cases h6 : (s.getReg .x10).toNat < 2^6
  · have hz6 := (word_shift_zero_iff (s.getReg .x10) 6).2 h6
    refine ⟨7, ?state1, by decide, ?trace, ?post⟩
    case trace =>
      write_step (.SRLI .x5 .x10 62)
      write_step (.BEQ .x5 .x0 24)
      write_step (.SRLI .x6 .x10 6)
      write_step (.BNE .x6 .x0 16)
      write_step (.ADDI .x5 .x0 1)
      write_step (.ADDI .x7 .x0 0)
      write_step (.JAL .x0 52)
      exact .nil _
    case post => simp [QuicSelected, getReg_setReg, Spec.Codec.QuicVarint.widthTag, h6]
  · have hn6 := word_shift_nonzero (s.getReg .x10) 6 (by omega)
    by_cases h14 : (s.getReg .x10).toNat < 2^14
    · have hz14 := (word_shift_zero_iff (s.getReg .x10) 14).2 h14
      refine ⟨9, ?state2, by decide, ?trace, ?post⟩
      case trace =>
        write_step (.SRLI .x5 .x10 62)
        write_step (.BEQ .x5 .x0 24)
        write_step (.SRLI .x6 .x10 6)
        write_step (.BNE .x6 .x0 16)
        write_step (.SRLI .x6 .x10 14)
        write_step (.BNE .x6 .x0 16)
        write_step (.ADDI .x5 .x0 2)
        write_step (.ADDI .x7 .x0 64)
        write_step (.JAL .x0 32)
        exact .nil _
      case post => simp [QuicSelected, getReg_setReg, Spec.Codec.QuicVarint.widthTag, h6, h14]
    · have hn14 := word_shift_nonzero (s.getReg .x10) 14 (by omega)
      by_cases h30 : (s.getReg .x10).toNat < 2^30
      · have hz30 := (word_shift_zero_iff (s.getReg .x10) 30).2 h30
        refine ⟨11, ?state4, by decide, ?trace, ?post⟩
        case trace =>
          write_step (.SRLI .x5 .x10 62)
          write_step (.BEQ .x5 .x0 24)
          write_step (.SRLI .x6 .x10 6)
          write_step (.BNE .x6 .x0 16)
          write_step (.SRLI .x6 .x10 14)
          write_step (.BNE .x6 .x0 16)
          write_step (.SRLI .x6 .x10 30)
          write_step (.BNE .x6 .x0 16)
          write_step (.ADDI .x5 .x0 4)
          write_step (.ADDI .x7 .x0 128)
          write_step (.JAL .x0 12)
          exact .nil _
        case post => simp [QuicSelected, getReg_setReg, Spec.Codec.QuicVarint.widthTag, h6, h14, h30]
      · have hn30 := word_shift_nonzero (s.getReg .x10) 30 (by omega)
        refine ⟨10, ?state8, by decide, ?trace, ?post⟩
        case trace =>
          write_step (.SRLI .x5 .x10 62)
          write_step (.BEQ .x5 .x0 24)
          write_step (.SRLI .x6 .x10 6)
          write_step (.BNE .x6 .x0 16)
          write_step (.SRLI .x6 .x10 14)
          write_step (.BNE .x6 .x0 16)
          write_step (.SRLI .x6 .x10 30)
          write_step (.BNE .x6 .x0 16)
          write_step (.ADDI .x5 .x0 8)
          write_step (.ADDI .x7 .x0 192)
          exact .nil _
        case post => simp [QuicSelected, getReg_setReg, Spec.Codec.QuicVarint.widthTag, h6, h14, h30]

end Libp2pAsm.Refinement.AsmCodec
