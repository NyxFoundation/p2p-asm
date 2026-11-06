import Libp2pAsm.Refinement.AsmDer.Programs
import Libp2pAsm.Refinement.AsmProtobuf.ReadBounds

namespace Libp2pAsm.Refinement.AsmDer
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def LengthInv (s : State) (bytes : List UInt8) (acc tag header remaining : Word) : Prop :=
  s.getReg .x13=acc ∧ s.getReg .x12=tag ∧ s.getReg .x14=header ∧ s.getReg .x16=remaining ∧
    s.getReg .x17=BitVec.ofNat 64 bytes.length ∧ s.getReg .x1=0 ∧
      Reads s.memory (s.getReg .x15) bytes

theorem length_byte (s : State) (b : UInt8) (bs : List UInt8) (acc tag header remaining : Word)
    (hl : (b::bs).length < 2^64) (hi : LengthInv s (b::bs) acc tag header remaining) :
    ∃ t, ReadTrace decoder 0 [(1,s.getReg .x15)] 7 (atPC s 66428) t ∧ t.pc=66428 ∧
      LengthInv t bs (acc <<< (8 : Nat) ||| BitVec.ofNat 64 b.toNat) tag header remaining ∧
      t.getReg .x15=s.getReg .x15+1 := by
  rcases hi with ⟨ha,htag,hh,hr,hn,hra,hread⟩
  have hne : s.getReg .x17≠0 := by rw [hn]; exact word_length_nonzero _ hl (by simp)
  have hbyte := hread.head
  refine ⟨?_,?trace,?post⟩
  case trace =>
    repeat parser_read_step
    exact .nil _
  case post =>
    have hd := word_succ_decrement bs.length
    simp_all [LengthInv,getReg_setReg]
    exact hread.tail

/-- The long-header loop reads exactly its count, with no content or guard loads. -/
theorem length_loop (bytes : List UInt8) (s : State) (acc tag header remaining : Word)
    (hl : bytes.length < 2^64) (hi : LengthInv s bytes acc tag header remaining) :
    ∃ t, ReadTrace decoder 0 (AsmProtobuf.Footprint.byteReads (s.getReg .x15) bytes.length)
      (7*bytes.length+1) (atPC s 66428) t ∧ t.pc=66456 ∧
      t.getReg .x13=foldBytes bytes acc ∧ t.getReg .x12=tag ∧
      t.getReg .x14=header ∧ t.getReg .x16=remaining ∧ t.getReg .x1=0 := by
  induction bytes generalizing s acc with
  | nil =>
    rcases hi with ⟨ha,htag,hh,hr,hn,hra,hread⟩
    refine ⟨?_,?trace,?post⟩
    case trace =>
      parser_read_step
      exact .nil _
    case post => simp [foldBytes,getReg_setReg,ha,htag,hh,hr,hra]
  | cons b bs ih =>
    obtain ⟨a,ha,hapc,hai,hptr⟩ := length_byte s b bs acc tag header remaining hl hi
    obtain ⟨t,ht,hpc,ho⟩ := ih a _ (by simp_all; omega) hai
    refine ⟨t,?_,hpc,ho⟩
    have path := ha.append (readTrace_at_pc hapc ht)
    simpa [AsmProtobuf.Footprint.byteReads,hptr,List.length_cons,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using path

theorem length_value_fits (bytes : List UInt8) (hl : bytes.length ≤ 8) :
    (bytes.foldl (fun n b => 256*n+b.toNat) 0) < 2^64 := by
  have hb := Codec.QuicVarint.fold_value_bound bytes 0 1 (by decide)
  have hp : 256^bytes.length ≤ 256^8 := Nat.pow_le_pow_right (by decide) hl
  simpa [Nat.mul_comm] using Nat.lt_of_lt_of_le hb (by simpa using hp)

theorem length_value_exact (bytes : List UInt8) (hl : bytes.length ≤ 8) :
    (foldBytes bytes 0).toNat=bytes.foldl (fun n b => 256*n+b.toNat) 0 := by
  have h := foldBytes_nat bytes 0
  have hb : bytes.foldl (fun n b => n*256+b.toNat) 0 < 18446744073709551616 := by
    simpa [Nat.mul_comm] using length_value_fits bytes hl
  simpa [Nat.mul_comm,Nat.mod_eq_of_lt hb] using h

end Libp2pAsm.Refinement.AsmDer
