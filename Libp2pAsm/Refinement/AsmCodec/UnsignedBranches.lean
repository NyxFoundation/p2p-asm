import Libp2pAsm.Refinement.AsmCodec.UnsignedRead

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000

theorem unsigned_empty (s : State) (acc count : Nat) (hi : UnsignedInv s [] acc count) :
    ∃ t, Trace unsignedDecode 0 5 (atPC s 65552) t ∧ t.pc = 0 ∧ Output 1 0 0 t := by
  rcases hi with ⟨hcount, hshift, hacc, hlimit, hlen, hra, hread⟩
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    trace_step (.BEQ .x11 .x0 144)
    trace_step (.ADDI .x10 .x0 1)
    trace_step (.ADDI .x11 .x0 0)
    trace_step (.ADDI .x12 .x0 0)
    trace_step (.JALR .x0 .x1 0)
    exact .nil _
  case post => simp [Output, getReg_setReg]

theorem unsigned_terminal_first (s : State) (b : UInt8) (bs : List UInt8) (acc : Nat)
    (hb : b.toNat < 128) (hi : UnsignedReadInv s (b :: bs) acc 0 b) :
    ∃ t, Trace unsignedDecode 0 7 (atPC s 65580) t ∧ t.pc = 0 ∧
      Output 0 (BitVec.ofNat 64 (acc + b.toNat % 128)) 1 t := by
  rcases hi with ⟨hcount, hshift, hacc, hpay, hflag, hlimit, hlen, hra, hread⟩
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    trace_step (.BNE .x30 .x0 76)
    trace_step (.ADDI .x30 .x0 1)
    trace_step (.BGEU .x30 .x6 48)
    trace_step (.ADDI .x11 .x28 0)
    trace_step (.ADDI .x12 .x6 0)
    trace_step (.ADDI .x10 .x0 0)
    trace_step (.JALR .x0 .x1 0)
    exact .nil _
  case post => simp [Output, getReg_setReg]

theorem unsigned_terminal_long (s : State) (b : UInt8) (bs : List UInt8) (acc count : Nat)
    (hc : 0 < count) (hc9 : count < 9) (hb : b.toNat < 128)
    (hi : UnsignedReadInv s (b :: bs) acc count b) :
    ∃ t, Trace unsignedDecode 0 8 (atPC s 65580) t ∧ t.pc = 0 ∧
      (if b.toNat % 128 = 0 then Output 3 0 0 t
       else Output 0 (BitVec.ofNat 64 (acc + b.toNat % 128 * 2^(7*count)))
         (BitVec.ofNat 64 (count+1)) t) := by
  rcases hi with ⟨hcount, hshift, hacc, hpay, hflag, hlimit, hlen, hra, hread⟩
  have hbranch : ¬BitVec.ofNat 64 (count + 1) ≤ (1 : Word) := by
    simp [BitVec.le_def]; omega
  by_cases hp : b.toNat % 128 = 0
  · refine ⟨?t, ?trace, ?post⟩
    case trace =>
      trace_step (.BNE .x30 .x0 76)
      trace_step (.ADDI .x30 .x0 1)
      trace_step (.BGEU .x30 .x6 48)
      trace_step (.BNE .x29 .x0 24)
      trace_step (.ADDI .x10 .x0 3)
      trace_step (.ADDI .x11 .x0 0)
      trace_step (.ADDI .x12 .x0 0)
      trace_step (.JALR .x0 .x1 0)
      exact .nil _
    case post => simp [hp, Output, getReg_setReg]
  · have hpn : BitVec.ofNat 64 (b.toNat % 128) ≠ (0 : Word) :=
      word_length_nonzero _ (by omega) (by omega)
    refine ⟨?t, ?trace, ?post⟩
    case trace =>
      trace_step (.BNE .x30 .x0 76)
      trace_step (.ADDI .x30 .x0 1)
      trace_step (.BGEU .x30 .x6 48)
      trace_step (.BNE .x29 .x0 24)
      trace_step (.ADDI .x11 .x28 0)
      trace_step (.ADDI .x12 .x6 0)
      trace_step (.ADDI .x10 .x0 0)
      trace_step (.JALR .x0 .x1 0)
      exact .nil _
    case post => simp [hp, Output, getReg_setReg]

theorem unsigned_overflow (s : State) (b : UInt8) (bs : List UInt8) (acc : Nat)
    (hb : ¬b.toNat < 128) (hi : UnsignedReadInv s (b :: bs) acc 8 b) :
    ∃ t, Trace unsignedDecode 0 6 (atPC s 65580) t ∧ t.pc = 0 ∧ Output 2 0 0 t := by
  rcases hi with ⟨hcount, hshift, hacc, hpay, hflag, hlimit, hlen, hra, hread⟩
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    trace_step (.BNE .x30 .x0 76)
    trace_step (.BNE .x6 .x31 24)
    trace_step (.ADDI .x10 .x0 2)
    trace_step (.ADDI .x11 .x0 0)
    trace_step (.ADDI .x12 .x0 0)
    trace_step (.JALR .x0 .x1 0)
    exact .nil _
  case post => simp [Output, getReg_setReg]

theorem unsigned_continue (s : State) (b : UInt8) (bs : List UInt8) (acc count : Nat)
    (hc : count < 8) (hb : ¬b.toNat < 128)
    (hi : UnsignedReadInv s (b :: bs) acc count b) :
    ∃ t, Trace unsignedDecode 0 6 (atPC s 65580) t ∧ t.pc = 65552 ∧
      UnsignedInv t bs (acc + b.toNat % 128 * 2^(7*count)) (count+1) := by
  rcases hi with ⟨hcount, hshift, hacc, hpay, hflag, hlimit, hlen, hra, hread⟩
  have hbranch : BitVec.ofNat 64 (count + 1) ≠ (9 : Word) := by
    intro he; have hn := congrArg BitVec.toNat he
    simp at hn; omega
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    trace_step (.BNE .x30 .x0 76)
    trace_step (.BNE .x6 .x31 24)
    trace_step (.ADDI .x10 .x10 1)
    trace_step (.ADDI .x11 .x11 (-1))
    trace_step (.ADDI .x7 .x7 7)
    trace_step (.JAL .x0 (-140))
    exact .nil _
  case post =>
    have hdec := word_succ_decrement bs.length
    have hshiftadd : BitVec.ofNat 64 (7*count) + (7 : Word) = BitVec.ofNat 64 (7*(count+1)) := by
      simp [Nat.mul_add, BitVec.ofNat_add]
    simp_all [UnsignedInv, getReg_setReg]
    exact hread.tail

end Libp2pAsm.Refinement.AsmCodec
