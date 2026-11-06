import Libp2pAsm.Refinement.AsmCodec.QuicLoop
import Libp2pAsm.Refinement.AsmCodec.QuicArithmetic
import Libp2pAsm.Refinement.AsmCodec.Safety
import Libp2pAsm.Refinement.AsmCodec.Errors

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000

theorem quic_decode_header (s : State) (b : UInt8) (bs : List UInt8)
    (hl : s.getReg .x11 ≠ 0) (hr : Reads s.memory (s.getReg .x10) (b :: bs)) :
    ∃ t, Trace quicDecode 0 5 (atPC s 65536) t ∧ t.pc = 65576 ∧
      t.getReg .x5 = BitVec.ofNat 64 b.toNat ∧
      t.getReg .x6 = BitVec.ofNat 64 (2^(b.toNat / 64)) ∧
      t.getReg .x10 = s.getReg .x10 ∧ t.getReg .x11 = s.getReg .x11 ∧
      t.memory = s.memory := by
  have hread := hr.head
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    trace_step (.BNE .x11 .x0 24)
    trace_step (.LBU .x5 .x10 0)
    trace_step (.SRLI .x7 .x5 6)
    trace_step (.ADDI .x6 .x0 1)
    trace_step (.SLL .x6 .x6 .x7)
    exact .nil _
  case post =>
    simp [getReg_setReg]
    simpa using quic_width_word b

theorem quic_decode_short (s : State) (hra : s.getReg .x1 = 0)
    (hl : s.getReg .x11 < s.getReg .x6) :
    ∃ t, Trace quicDecode 0 5 (atPC s 65576) t ∧ t.pc = 0 ∧ Output 1 0 0 t := by
  have hn : ¬s.getReg .x6 ≤ s.getReg .x11 := by exact BitVec.not_le.mpr hl
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    trace_step (.BGEU .x11 .x6 24)
    trace_step (.ADDI .x10 .x0 1)
    trace_step (.ADDI .x11 .x0 0)
    trace_step (.ADDI .x12 .x0 0)
    trace_step (.JALR .x0 .x1 0)
    exact .nil _
  case post => simp [Output, getReg_setReg]

theorem quic_decode_enter (s : State) (b : UInt8)
    (hb : s.getReg .x5 = BitVec.ofNat 64 b.toNat)
    (hl : s.getReg .x6 ≤ s.getReg .x11) :
    ∃ t, Trace quicDecode 0 4 (atPC s 65576) t ∧ t.pc = 65612 ∧
      t.getReg .x7 = s.getReg .x6 + (-1) ∧
      t.getReg .x28 = BitVec.ofNat 64 (b.toNat % 64) ∧
      t.getReg .x10 = s.getReg .x10 + 1 ∧ t.getReg .x6 = s.getReg .x6 ∧
      t.memory = s.memory := by
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    trace_step (.BGEU .x11 .x6 24)
    trace_step (.ANDI .x28 .x5 63)
    trace_step (.ADDI .x10 .x10 1)
    trace_step (.ADDI .x7 .x6 (-1))
    exact .nil _
  case post =>
    simp [getReg_setReg]
    exact quic_payload_word b

theorem quic_decode_finish (s : State) (hra : s.getReg .x1 = 0) :
    ∃ t, Trace quicDecode 0 4 (atPC s 65640) t ∧ t.pc = 0 ∧
      Output 0 (s.getReg .x28) (s.getReg .x6) t := by
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    trace_step (.ADDI .x11 .x28 0)
    trace_step (.ADDI .x12 .x6 0)
    trace_step (.ADDI .x10 .x0 0)
    trace_step (.JALR .x0 .x1 0)
    exact .nil _
  case post => simp [Output, getReg_setReg]

end Libp2pAsm.Refinement.AsmCodec
