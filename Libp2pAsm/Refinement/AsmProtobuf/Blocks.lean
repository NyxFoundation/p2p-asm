import Libp2pAsm.Refinement.AsmProtobuf.Programs
import Libp2pAsm.Refinement.AsmProtobuf.Arithmetic
import Libp2pAsm.Rv64.Logic.ParserSymbolic
import Libp2pAsm.Rv64.Logic.ParserMemory

namespace Libp2pAsm.Refinement.AsmProtobuf
open Rv64 Rv64.Logic AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def Inv (s : State) (bytes : List UInt8) (acc count : Nat) : Prop :=
  s.getReg .x6 = BitVec.ofNat 64 count ∧ s.getReg .x7 = BitVec.ofNat 64 (7*count) ∧
  s.getReg .x28 = BitVec.ofNat 64 acc ∧ s.getReg .x11 = BitVec.ofNat 64 bytes.length ∧
  s.getReg .x1 = 0 ∧ Reads s.memory (s.getReg .x10) bytes

def ReadInv (s : State) (bytes : List UInt8) (acc count : Nat) (b : UInt8) : Prop :=
  s.getReg .x6 = BitVec.ofNat 64 (count+1) ∧ s.getReg .x7 = BitVec.ofNat 64 (7*count) ∧
  s.getReg .x28 = BitVec.ofNat 64 (acc+b.toNat%128*2^(7*count)) ∧
  s.getReg .x30 = (if b.toNat < 128 then 0 else 1) ∧
  s.getReg .x11 = BitVec.ofNat 64 bytes.length ∧ s.getReg .x1 = 0 ∧
  Reads s.memory (s.getReg .x10) bytes

theorem empty (s : State) (acc count : Nat) (hi : Inv s [] acc count) :
    ∃ t, Trace program 0 17 (atPC s 65640) t ∧ t.pc = 0 ∧ Post (.error .truncated) t := by
  rcases hi with ⟨hc, hs, ha, hl, hr, hm⟩
  refine ⟨?_, ?trace, ?post⟩
  case trace =>
    repeat parser_step
    exact .nil _
  case post => simp [Post, DecodePost, Output, errorCode, Cleared,
    Asm.Crypto.Sha2.cleared, getReg_setReg]

theorem read_prefix (s : State) (b : UInt8) (bs : List UInt8) (acc count : Nat)
    (hc : count ≤ 9) (hl : (b::bs).length < 2^64)
    (hg : count = 9 → b.toNat ≤ 1) (hi : Inv s (b::bs) acc count) :
    ∃ n t, n ≤ 7 ∧ Trace program 0 n (atPC s 65640) t ∧ t.pc = 65736 ∧
      Inv t (b::bs) acc count ∧ t.getReg .x5 = BitVec.ofNat 64 b.toNat := by
  rcases hi with ⟨hcount, hshift, hacc, hlen, hra, hread⟩
  have hn : s.getReg .x11 ≠ 0 := by
    rw [hlen]; exact word_length_nonzero _ hl (by simp)
  have hbyte := hread.head
  have hbranch : BitVec.ofNat 64 count = (9 : Word) ↔ count = 9 := by
    simp [← BitVec.toNat_inj]; omega
  by_cases hlast : count = 9
  · have hb : BitVec.ofNat 64 b.toNat ≤ (1 : Word) := by
      simpa [BitVec.le_def, byte_word_nat] using hg hlast
    refine ⟨7, ?_, by decide, ?trace, ?post⟩
    case trace =>
      repeat parser_step
      exact .nil _
    case post => simp_all [Inv, getReg_setReg]
  · have hb := mt hbranch.mp hlast
    refine ⟨4, ?_, by decide, ?trace, ?post⟩
    case trace =>
      repeat parser_step
      exact .nil _
    case post => simp_all [Inv, getReg_setReg]

theorem accumulate_trace (s : State) (b : UInt8) (bs : List UInt8) (acc count : Nat)
    (hc : count ≤ 9) (ha : acc < 2^(7*count))
    (hi : Inv s (b::bs) acc count) (hbyte : s.getReg .x5 = BitVec.ofNat 64 b.toNat) :
    ∃ t, Trace program 0 5 (atPC s 65736) t ∧ t.pc = 65756 ∧
      ReadInv t (b::bs) acc count b := by
  rcases hi with ⟨hcount, hshift, hacc, hlen, hra, hread⟩
  have hadd := accumulate acc count b hc ha
  have hflag := unsigned_flag_word b
  refine ⟨?_, ?trace, ?post⟩
  case trace =>
    repeat parser_step
    exact .nil _
  case post => simp_all [ReadInv, getReg_setReg, BitVec.ofNat_add]

theorem read (s : State) (b : UInt8) (bs : List UInt8) (acc count : Nat)
    (hc : count ≤ 9) (ha : acc < 2^(7*count)) (hl : (b::bs).length < 2^64)
    (hg : count = 9 → b.toNat ≤ 1) (hi : Inv s (b::bs) acc count) :
    ∃ n t, n ≤ 12 ∧ Trace program 0 n (atPC s 65640) t ∧ t.pc = 65756 ∧
      ReadInv t (b::bs) acc count b := by
  obtain ⟨n, a, hn, ht, hp, hi, hb⟩ := read_prefix s b bs acc count hc hl hg hi
  obtain ⟨t, hu, hpc, ho⟩ := accumulate_trace a b bs acc count hc ha hi hb
  exact ⟨n+5,t,by omega,ht.append (trace_at_pc hp hu),hpc,ho⟩

theorem overflow (s : State) (b : UInt8) (bs : List UInt8) (acc : Nat)
    (hl : (b::bs).length < 2^64) (hb : 1 < b.toNat) (hi : Inv s (b::bs) acc 9) :
    ∃ t, Trace program 0 22 (atPC s 65640) t ∧ t.pc = 0 ∧ Post (.error .overflow) t := by
  rcases hi with ⟨hcount, hshift, hacc, hlen, hra, hread⟩
  have hn : s.getReg .x11 ≠ 0 := by
    rw [hlen]; exact word_length_nonzero _ hl (by simp)
  have hbyte := hread.head
  have hlarge : ¬BitVec.ofNat 64 b.toNat ≤ (1 : Word) := by
    simp [BitVec.le_def, byte_word_nat]; omega
  refine ⟨?_, ?trace, ?post⟩
  case trace =>
    repeat parser_step
    exact .nil _
  case post => simp [Post, DecodePost, Output, errorCode, Cleared,
    Asm.Crypto.Sha2.cleared, getReg_setReg]

theorem terminal (s : State) (b : UInt8) (bs : List UInt8) (acc count : Nat)
    (hb : b.toNat < 128) (hi : ReadInv s (b::bs) acc count b) :
    ∃ t, Trace program 0 17 (atPC s 65756) t ∧ t.pc = 0 ∧
      Post (.ok ⟨acc+b.toNat%128*2^(7*count),count+1⟩) t := by
  rcases hi with ⟨hcount, hshift, hacc, hflag, hlen, hra, hread⟩
  refine ⟨?_, ?trace, ?post⟩
  case trace =>
    repeat parser_step
    exact .nil _
  case post => simp [Post, DecodePost, Output, Cleared,
    Asm.Crypto.Sha2.cleared, getReg_setReg]

theorem continuation (s : State) (b : UInt8) (bs : List UInt8) (acc count : Nat)
    (hb : ¬b.toNat < 128) (hi : ReadInv s (b::bs) acc count b) :
    ∃ t, Trace program 0 5 (atPC s 65756) t ∧ t.pc = 65640 ∧
      Inv t bs (acc+b.toNat%128*2^(7*count)) (count+1) := by
  rcases hi with ⟨hcount, hshift, hacc, hflag, hlen, hra, hread⟩
  refine ⟨?_, ?trace, ?post⟩
  case trace =>
    repeat parser_step
    exact .nil _
  case post =>
    have hdec := word_succ_decrement bs.length
    have hshiftadd : BitVec.ofNat 64 (7*count)+(7 : Word) = BitVec.ofNat 64 (7*(count+1)) := by
      simp [Nat.mul_add, BitVec.ofNat_add]
    simp_all [Inv, getReg_setReg]
    exact hread.tail

end Libp2pAsm.Refinement.AsmProtobuf
