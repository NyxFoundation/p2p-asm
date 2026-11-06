import Libp2pAsm.Refinement.AsmDer.EncodeOutput
import Libp2pAsm.Rv64.Logic.ParserStore

namespace Libp2pAsm.Refinement.AsmDer.Encode
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def reverseWrites (base : Word) (offset : Nat) : Nat → List (Nat × Word)
  | 0 => []
  | n+1 => (1,base+BitVec.ofNat 64 (offset+n))::reverseWrites base offset n

def EmitInv (s : State) (base : Word) (offset value count : Nat) (header : Word)
    (bytes : Array UInt8) (frame : List Region) : Prop :=
  s.getReg .x11=BitVec.ofNat 64 value ∧ s.getReg .x29=BitVec.ofNat 64 count ∧
    s.getReg .x30=base+BitVec.ofNat 64 (offset+count)-1 ∧ s.getReg .x31=header ∧
    s.getReg .x1=0 ∧ s.memory=heap base bytes true frame

theorem emit_advance (s : State) (value count : Nat) (hv : value<2^64)
    (hvalue : s.getReg .x11=BitVec.ofNat 64 value)
    (hcount : s.getReg .x29=BitVec.ofNat 64 (count+1)) :
    ∃ t, AccessTrace encoder 0 [] [] 4 (atPC s 66020) t ∧ t.pc=66012 ∧
      t.getReg .x11=BitVec.ofNat 64 (value/256) ∧ t.getReg .x29=BitVec.ofNat 64 count ∧
      t.getReg .x30=s.getReg .x30-1 ∧ t.getReg .x31=s.getReg .x31 ∧
      t.getReg .x1=s.getReg .x1 ∧ t.memory=s.memory := by
  have hshift := shift_byte_nat value hv
  have hdecr := word_succ_decrement count
  refine ⟨?_,?trace,?post⟩
  case trace =>
    repeat parser_access_step
    exact .nil _
  case post => simp_all [getReg_setReg,BitVec.sub_eq_add_neg]

theorem emit_step (s : State) (base : Word) (offset value count : Nat) (header : Word)
    (bytes : Array UInt8) (frame : List Region) (hc : count<8) (hv : value<2^64)
    (hi : offset+(count+1)≤bytes.size) (hb : base.toNat+bytes.size≤2^64)
    (hm : (heap base bytes true frame).valid=true)
    (hinv : EmitInv s base offset value (count+1) header bytes frame) :
    ∃ t, AccessTrace encoder 0 [] [(1,base+BitVec.ofNat 64 (offset+count))] 6 (atPC s 66012) t ∧
      t.pc=66012 ∧ EmitInv t base offset (value/256) count header
        (bytes.setIfInBounds (offset+count) value.toUInt8) frame := by
  rcases hinv with ⟨hvalue,hcount,hptr,hheader,hra,hmem⟩
  have hn : s.getReg .x29≠0 := by rw [hcount]; exact word_length_nonzero _ (by omega) (by omega)
  have hptr' : s.getReg .x30=base+BitVec.ofNat 64 (offset+count) := by
    rw [hptr,←Nat.add_assoc,BitVec.ofNat_add,←BitVec.add_assoc]
    exact BitVec.add_sub_cancel _ _
  clear hptr
  have hstart : AccessTrace encoder 0 [] [] 1 (atPC s 66012) (atPC s 66016) := by
    parser_access_step
    exact .nil _
  obtain ⟨a,ha,hapc,ham,hareg⟩ := store_byte encoder 66016 s .x30 .x11 0 base
    (BitVec.ofNat 64 value) (offset+count) bytes frame rfl (by decide)
    (by simpa using hptr') hvalue hmem hm hb (by omega)
  obtain ⟨t,ht,hpc,htvalue,htcount,htptr,hth,ht1,htm⟩ := emit_advance a value count hv
    ((hareg .x11).trans hvalue) ((hareg .x29).trans hcount)
  refine ⟨t,?_,hpc,htvalue,htcount,?_,(hth.trans (hareg .x31)).trans hheader,
    (ht1.trans (hareg .x1)).trans hra,?_⟩
  · simpa using (hstart.append ha).append (accessTrace_at_pc hapc ht)
  · rw [htptr,hareg .x30,hptr']
  · rw [htm,ham]
    simp [Nat.mod_eq_of_lt hv]

theorem emit_loop (count : Nat) (s : State) (base : Word) (offset value : Nat) (header : Word)
    (bytes : Array UInt8) (frame : List Region) (hc : count≤8) (hv : value<2^64)
    (hi : offset+count≤bytes.size) (hb : base.toNat+bytes.size≤2^64)
    (hm : (heap base bytes true frame).valid=true)
    (hinv : EmitInv s base offset value count header bytes frame) :
    ∃ t, AccessTrace encoder 0 [] (reverseWrites base offset count) (6*count+1) (atPC s 66012) t ∧
      t.pc=66036 ∧ t.getReg .x31=header ∧ t.getReg .x1=0 ∧
      t.memory=heap base (reversePatch bytes offset value count) true frame := by
  induction count generalizing s value bytes with
  | zero =>
    rcases hinv with ⟨hvalue,hcount,hptr,hheader,hra,hmem⟩
    refine ⟨?_,?trace,?post⟩
    case trace =>
      parser_access_step
      exact .nil _
    case post => simp [getReg_setReg,hheader,hra,hmem,reversePatch]
  | succ count ih =>
    obtain ⟨a,ha,hapc,hai⟩ := emit_step s base offset value count header bytes frame
      (by omega) hv hi hb hm hinv
    have hm' : (heap base (bytes.setIfInBounds (offset+count) value.toUInt8) true frame).valid=true := by
      rw [←heap_valid_congr base bytes _ true frame (by simp)]; exact hm
    obtain ⟨t,ht,hpc,ho⟩ := ih a (value/256) _ (by omega) (by omega)
      (by simp; omega) (by simpa using hb) hm' hai
    exact ⟨t,by simpa [reverseWrites,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (ha.append (accessTrace_at_pc hapc ht)),hpc,ho⟩

end Libp2pAsm.Refinement.AsmDer.Encode
