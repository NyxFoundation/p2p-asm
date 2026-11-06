import Libp2pAsm.Refinement.AsmCodec.Programs
import Libp2pAsm.Rv64.Logic.Symbolic
import Libp2pAsm.Rv64.Logic.Bytes

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

theorem word_length_nonzero (n : Nat) (hn : n < 2^64) (hp : 0 < n) :
    BitVec.ofNat 64 n ≠ (0 : Word) := by
  intro he
  have he' := congrArg BitVec.toNat he
  simp [Nat.mod_eq_of_lt hn] at he'
  omega

theorem word_succ_decrement (n : Nat) :
    BitVec.ofNat 64 (n + 1) + (-1 : Word) = BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_add]
  change BitVec.ofNat 64 n + (1 : Word) + (-1 : Word) = _
  rw [BitVec.add_assoc, BitVec.add_right_neg, BitVec.add_zero]

theorem quic_tail_iteration (s : State) (b : UInt8) (bs : List UInt8)
    (hl : bs.length < 7) (hc : s.getReg .x7 = BitVec.ofNat 64 (bs.length + 1))
    (hr : Reads s.memory (s.getReg .x10) (b :: bs)) :
    ∃ t, Trace quicDecode 0 7 (atPC s 65612) t ∧ t.pc = 65612 ∧
      Reads t.memory (t.getReg .x10) bs ∧ t.getReg .x7 = BitVec.ofNat 64 bs.length ∧
      t.getReg .x28 = (s.getReg .x28 <<< (8 : Nat) ||| BitVec.ofNat 64 b.toNat) ∧
      t.getReg .x6 = s.getReg .x6 := by
  have hn := word_length_nonzero (bs.length + 1) (by omega) (by omega)
  have hread := hr.head
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    trace_step (.BEQ .x7 .x0 28)
    trace_step (.SLLI .x28 .x28 8)
    trace_step (.LBU .x29 .x10 0)
    trace_step (.OR .x28 .x28 .x29)
    trace_step (.ADDI .x10 .x10 1)
    trace_step (.ADDI .x7 .x7 (-1))
    trace_step (.JAL .x0 (-24))
    exact .nil _
  case post =>
    simp [getReg_setReg]
    exact ⟨hr.tail, word_succ_decrement _⟩

/-- The entire QUIC tail loop, for all byte values and every permitted iteration count. -/
theorem quic_tail_loop (bytes : List UInt8) (s : State) (hl : bytes.length ≤ 7)
    (hc : s.getReg .x7 = BitVec.ofNat 64 bytes.length)
    (hr : Reads s.memory (s.getReg .x10) bytes) :
    ∃ t, Trace quicDecode 0 (7 * bytes.length + 1) (atPC s 65612) t ∧
      t.pc = 65640 ∧ t.getReg .x28 = foldBytes bytes (s.getReg .x28) ∧
      t.getReg .x6 = s.getReg .x6 := by
  induction bytes generalizing s with
  | nil =>
    refine ⟨?t, ?trace, ?post⟩
    case trace =>
      trace_step (.BEQ .x7 .x0 28)
      exact .nil _
    case post => simp [foldBytes]
  | cons b bs ih =>
    obtain ⟨t, ht, hpc, hread, hcount, hacc, hwidth⟩ :=
      quic_tail_iteration s b bs (by simp only [List.length_cons] at hl; omega) hc hr
    obtain ⟨u, hu, hupc, huacc, huwidth⟩ := ih t (by simp_all; omega) hcount hread
    have hjoin : atPC t 65612 = t := by rw [← hpc, atPC_self]
    rw [hjoin] at hu
    refine ⟨u, ?_, hupc, ?_, huwidth.trans hwidth⟩
    · simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht.append hu
    · simpa [foldBytes, hacc] using huacc

end Libp2pAsm.Refinement.AsmCodec
