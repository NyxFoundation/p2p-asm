import Libp2pAsm.Rv64.Logic.WriteTrace
import Libp2pAsm.Refinement.AsmCodec.QuicEncodeCorrect
import Libp2pAsm.Refinement.Codec.UnsignedHelpers

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

variable {lower upper : Nat}

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768

def CountInv (s : State) (value count : Nat) : Prop :=
  s.getReg .x5 = BitVec.ofNat 64 value ∧ s.getReg .x6 = BitVec.ofNat 64 count ∧ s.getReg .x7 = 128

def SameInputs (s t : State) : Prop :=
  t.getReg .x10 = s.getReg .x10 ∧ t.getReg .x11 = s.getReg .x11 ∧
  t.getReg .x12 = s.getReg .x12 ∧ t.memory = s.memory

theorem SameInputs.trans {s t u : State} (h : SameInputs s t) (k : SameInputs t u) : SameInputs s u :=
  ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1, k.2.2.2.trans h.2.2.2⟩

theorem shift_word_nat (value : Nat) (hv : value < 2^64) :
    BitVec.ofNat 64 value >>> (7 : Nat) = BitVec.ofNat 64 (value / 128) := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hv]
  omega

theorem unsigned_count_step (s : State) (value count : Nat) (hv : value < 2^64)
    (hn : ¬value < 128) (hi : CountInv s value count) :
    ∃ t, WriteTrace unsignedEncode 0 lower upper 4 (atPC s 65576) t ∧ t.pc = 65576 ∧
      CountInv t (value / 128) (count+1) ∧ SameInputs s t := by
  rcases hi with ⟨hvalue, hcount, hlimit⟩
  have hbranch : ¬BitVec.ofNat 64 value < (128 : Word) := by
    simpa [BitVec.lt_def, Nat.mod_eq_of_lt hv] using hn
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    write_step (.BLTU .x5 .x7 16)
    write_step_plain (.SRLI .x5 .x5 7)
    write_step_plain (.ADDI .x6 .x6 1)
    write_step_plain (.JAL .x0 (-12))
    exact .nil _
  case post =>
    simp [CountInv, SameInputs, getReg_setReg]
    refine ⟨?_, ?_, hlimit⟩
    · rw [hvalue]; exact shift_word_nat value hv
    · rw [hcount, BitVec.ofNat_add]

theorem unsigned_count_stop (s : State) (value count : Nat) (hv : value < 128)
    (hi : CountInv s value count) :
    ∃ t, WriteTrace unsignedEncode 0 lower upper 1 (atPC s 65576) t ∧ t.pc = 65592 ∧
      t.getReg .x6 = BitVec.ofNat 64 count ∧ SameInputs s t := by
  rcases hi with ⟨hvalue, hcount, hlimit⟩
  have hbranch : BitVec.ofNat 64 value < (128 : Word) := by simp [BitVec.lt_def]; omega
  refine ⟨?t, ?trace, ?post⟩
  case trace =>
    write_step (.BLTU .x5 .x7 16)
    exact .nil _
  case post => simp [SameInputs, hcount]

/-- Counting constructs the spec encoding witness; it assumes only a representable value bound. -/
theorem unsigned_count_loop (fuel : Nat) (s : State) (value count : Nat)
    (hf : 0 < fuel) (hf9 : fuel ≤ 9) (hv : value < 128^fuel) (hi : CountInv s value count) :
    ∃ encoded n t, Spec.Codec.UnsignedVarint.encodeLoop fuel value = .ok encoded ∧
      0 < encoded.length ∧ encoded.length ≤ fuel ∧ n ≤ 4*fuel ∧
      WriteTrace unsignedEncode 0 lower upper n (atPC s 65576) t ∧ t.pc = 65592 ∧
      t.getReg .x6 = BitVec.ofNat 64 (count + encoded.length - 1) ∧ SameInputs s t := by
  induction fuel generalizing s value count with
  | zero => omega
  | succ fuel ih =>
    by_cases hn : value < 128
    · obtain ⟨t, ht, hp, hw, hs⟩ := unsigned_count_stop (lower := lower) (upper := upper) s value count hn hi
      exact ⟨[value.toUInt8], 1, t, by simp [Codec.UnsignedVarint.encodeLoop_step, hn],
        by simp, by simp, by omega, ht, hp, by simpa using hw, hs⟩
    · have hp := Nat.pow_le_pow_right (by decide : 0 < 128) hf9
      have hv64 : value < 2^64 := by omega
      obtain ⟨a, ha, hapc, hai, has⟩ := unsigned_count_step (lower := lower) (upper := upper) s value count hv64 hn hi
      have hv' : value / 128 < 128^fuel := by
        apply (Nat.div_lt_iff_lt_mul (by decide)).2
        simpa [Nat.pow_succ] using hv
      have hfpos : 0 < fuel := by cases fuel <;> simp_all
      obtain ⟨tail, n, t, he, hpos, hlen, hbound, ht, htpc, hw, hs⟩ :=
        ih a (value/128) (count+1) hfpos (by omega) hv' hai
      refine ⟨(value % 128 + 128).toUInt8 :: tail, 4+n, t, ?_, by simp, by simpa using Nat.succ_le_succ hlen,
        by omega, ha.append (writeTrace_at_pc hapc ht), htpc, ?_, has.trans hs⟩
      · simp [Codec.UnsignedVarint.encodeLoop_step, hn, he]
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw

end Libp2pAsm.Refinement.AsmCodec
