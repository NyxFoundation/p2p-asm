import Libp2pAsm.Refinement.AsmCodec.Programs
import Libp2pAsm.Rv64.Logic.WriteTrace
import Libp2pAsm.Spec.Codec.QuicVarint
import Libp2pAsm.Spec.Codec.UnsignedVarint

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

variable {lower upper : Nat}

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem quic_encode_overflow_trace (s : State) (hra : s.getReg .x1 = 0)
    (hv : s.getReg .x10 >>> 62 ≠ 0) :
    ∃ t, WriteTrace quicEncode 0 lower upper 6 (atPC s 0x10000) t ∧
      t.pc = 0 ∧ Output 2 0 0 t ∧ t.memory = s.memory := by
  refine ⟨atPC ((((s.setReg .x5 (s.getReg .x10 >>> 62)).setReg .x10 2).setReg .x11 0).setReg .x12 0) 0, ?trace, ?post⟩
  case trace =>
    write_step (.SRLI .x5 .x10 62)
    write_step (.BEQ .x5 .x0 24)
    write_step (.ADDI .x10 .x0 2)
    write_step (.ADDI .x11 .x0 0)
    write_step (.ADDI .x12 .x0 0)
    write_step (.JALR .x0 .x1 0)
    exact .nil _
  case post => simp [Output, getReg_setReg]

theorem unsigned_encode_overflow_trace (s : State) (hra : s.getReg .x1 = 0)
    (hv : s.getReg .x10 >>> 63 ≠ 0) :
    ∃ t, WriteTrace unsignedEncode 0 lower upper 6 (atPC s 0x10000) t ∧
      t.pc = 0 ∧ Output 2 0 0 t ∧ t.memory = s.memory := by
  refine ⟨atPC ((((s.setReg .x5 (s.getReg .x10 >>> 63)).setReg .x10 2).setReg .x11 0).setReg .x12 0) 0,
    ?trace, ?post⟩
  case trace =>
    write_step (.SRLI .x5 .x10 63)
    write_step (.BEQ .x5 .x0 24)
    write_step (.ADDI .x10 .x0 2)
    write_step (.ADDI .x11 .x0 0)
    write_step (.ADDI .x12 .x0 0)
    write_step (.JALR .x0 .x1 0)
    exact .nil _
  case post => simp [Output, getReg_setReg]

theorem quic_decode_empty_trace (s : State) (hra : s.getReg .x1 = 0)
    (hl : s.getReg .x11 = 0) :
    ∃ t, Trace quicDecode 0 5 (atPC s 0x10000) t ∧
      t.pc = 0 ∧ Output 1 0 0 t ∧ t.memory = s.memory := by
  refine ⟨atPC (((s.setReg .x10 1).setReg .x11 0).setReg .x12 0) 0, ?trace, ?post⟩
  case trace =>
    trace_step (.BNE .x11 .x0 24)
    trace_step (.ADDI .x10 .x0 1)
    trace_step (.ADDI .x11 .x0 0)
    trace_step (.ADDI .x12 .x0 0)
    trace_step (.JALR .x0 .x1 0)
    exact .nil _
  case post => simp [Output, getReg_setReg]

theorem unsigned_decode_empty_trace (s : State) (hra : s.getReg .x1 = 0)
    (hl : s.getReg .x11 = 0) :
    ∃ t, Trace unsignedDecode 0 9 (atPC s 0x10000) t ∧
      t.pc = 0 ∧ Output 1 0 0 t ∧ t.memory = s.memory := by
  let scratch := (((s.setReg .x6 0).setReg .x7 0).setReg .x28 0).setReg .x31 9
  refine ⟨atPC (((scratch.setReg .x10 1).setReg .x11 0).setReg .x12 0) 0, ?trace, ?post⟩
  case trace =>
    trace_step (.ADDI .x6 .x0 0)
    trace_step (.ADDI .x7 .x0 0)
    trace_step (.ADDI .x28 .x0 0)
    trace_step (.ADDI .x31 .x0 9)
    trace_step (.BEQ .x11 .x0 144)
    trace_step (.ADDI .x10 .x0 1)
    trace_step (.ADDI .x11 .x0 0)
    trace_step (.ADDI .x12 .x0 0)
    trace_step (.JALR .x0 .x1 0)
    exact .nil _
  case post => simp [scratch, Output, getReg_setReg]

end Libp2pAsm.Refinement.AsmCodec
