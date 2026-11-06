import Libp2pAsm.Refinement.AsmCodec.QuicCorrect
import Libp2pAsm.Refinement.AsmCodec.UnsignedArithmetic

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000

/-- Registers and actual readable bytes at the unsigned decoder loop header. -/
def UnsignedInv (s : State) (bytes : List UInt8) (acc count : Nat) : Prop :=
  s.getReg .x6 = BitVec.ofNat 64 count ∧ s.getReg .x7 = BitVec.ofNat 64 (7*count) ∧
  s.getReg .x28 = BitVec.ofNat 64 acc ∧ s.getReg .x31 = 9 ∧
  s.getReg .x11 = BitVec.ofNat 64 bytes.length ∧ s.getReg .x1 = 0 ∧
  Reads s.memory (s.getReg .x10) bytes

def UnsignedReadInv (s : State) (bytes : List UInt8) (acc count : Nat) (b : UInt8) : Prop :=
  s.getReg .x6 = BitVec.ofNat 64 (count+1) ∧ s.getReg .x7 = BitVec.ofNat 64 (7*count) ∧
  s.getReg .x28 = BitVec.ofNat 64 (acc + b.toNat % 128 * 2^(7*count)) ∧
  s.getReg .x29 = BitVec.ofNat 64 (b.toNat % 128) ∧
  s.getReg .x30 = (if b.toNat < 128 then 0 else 1) ∧ s.getReg .x31 = 9 ∧
  s.getReg .x11 = BitVec.ofNat 64 bytes.length ∧ s.getReg .x1 = 0 ∧
  Reads s.memory (s.getReg .x10) bytes

theorem unsigned_read (s : State) (b : UInt8) (bs : List UInt8) (acc count : Nat)
    (hc : count < 9) (ha : acc < 2^(7*count)) (hl : (b :: bs).length < 2^64)
    (hi : UnsignedInv s (b :: bs) acc count) :
    ∃ t, Trace unsignedDecode 0 7 (atPC s 65552) t ∧ t.pc = 65580 ∧
      UnsignedReadInv t (b :: bs) acc count b := by
  rcases hi with ⟨hcount, hshift, hacc, hlimit, hlen, hra, hread⟩
  have hn : s.getReg .x11 ≠ 0 := by
    rw [hlen]; exact word_length_nonzero _ hl (by simp)
  have hbyte := hread.head
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    trace_step (.BEQ .x11 .x0 144)
    trace_step (.LBU .x5 .x10 0)
    trace_step (.ANDI .x29 .x5 127)
    trace_step (.SLL .x30 .x29 .x7)
    trace_step (.OR .x28 .x28 .x30)
    trace_step (.ADDI .x6 .x6 1)
    trace_step (.SRLI .x30 .x5 7)
    exact .nil _
  case post =>
    have hpayload := unsigned_payload_word b
    have hflag := unsigned_flag_word b
    have hadd := unsigned_accumulate acc count b hc ha
    simp_all [UnsignedReadInv, getReg_setReg, BitVec.ofNat_add]

theorem unsigned_initialize (s : State) (bytes : List UInt8)
    (hlen : s.getReg .x11 = BitVec.ofNat 64 bytes.length)
    (hra : s.getReg .x1 = 0) (hr : Reads s.memory (s.getReg .x10) bytes) :
    ∃ t, Trace unsignedDecode 0 4 (atPC s 65536) t ∧ t.pc = 65552 ∧
      UnsignedInv t bytes 0 0 := by
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    trace_step (.ADDI .x6 .x0 0)
    trace_step (.ADDI .x7 .x0 0)
    trace_step (.ADDI .x28 .x0 0)
    trace_step (.ADDI .x31 .x0 9)
    exact .nil _
  case post => simp [UnsignedInv, getReg_setReg, hlen, hra, hr]

end Libp2pAsm.Refinement.AsmCodec
