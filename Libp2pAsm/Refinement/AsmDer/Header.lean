import Libp2pAsm.Refinement.AsmDer.Prefix
import Libp2pAsm.Refinement.AsmDer.LengthLoop

namespace Libp2pAsm.Refinement.AsmDer
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def HeaderInv (s : State) (tail : List UInt8) (tag first : UInt8) (ptr : Word) : Prop :=
  s.getReg .x12=BitVec.ofNat 64 tag.toNat ∧ s.getReg .x13=BitVec.ofNat 64 first.toNat ∧
    s.getReg .x14=2 ∧ s.getReg .x15=ptr+2 ∧ s.getReg .x16=BitVec.ofNat 64 tail.length ∧
    s.getReg .x1=0 ∧ Reads s.memory (ptr+2) tail

theorem second_byte (s : State) (tag first : UInt8) (tail : List UInt8) (ptr : Word)
    (hl : (tag::first::tail).length < 2^64) (hi : TagInv s (tag::first::tail) tag ptr) :
    ∃ t, ReadTrace decoder 0 [(1,ptr+1)] 8 (atPC s 65936) t ∧
      t.pc=(if first.toNat < 128 then 66536 else 66036) ∧ HeaderInv t tail tag first ptr := by
  rcases hi with ⟨htag,hptr,hlen,hra,hread⟩
  simp only [List.length_cons] at hl
  have hlen2 : (2 : Word) ≤ s.getReg .x11 := by
    rw [hlen]; simp [BitVec.le_def,Nat.mod_eq_of_lt hl]
  have hbyte := hread.tail.head
  have htail : Reads s.memory (ptr+2) tail := by simpa [BitVec.add_assoc] using hread.tail.tail
  have hdec : BitVec.ofNat 64 (tag::first::tail).length+(18446744073709551614 : Word) =
      BitVec.ofNat 64 tail.length := by
    simp [BitVec.ofNat_add,BitVec.add_assoc]
  have hp : ∃ a, ReadTrace decoder 0 [(1,ptr+1)] 3 (atPC s 65936) a ∧
      a.pc=66016 ∧ a.getReg .x12=BitVec.ofNat 64 tag.toNat ∧
      a.getReg .x13=BitVec.ofNat 64 first.toNat ∧ a.getReg .x10=ptr ∧
      a.getReg .x11=BitVec.ofNat 64 (tag::first::tail).length ∧
      a.getReg .x1=0 ∧ Reads a.memory (ptr+2) tail := by
    refine ⟨?_,?trace,?post⟩
    case trace =>
      repeat parser_read_step
      exact .nil _
    case post => simp_all [getReg_setReg]
  obtain ⟨a,ha,hpc,ha12,ha13,ha10,ha11,ha1,ham⟩ := hp
  have hs : ∃ t, ReadTrace decoder 0 [] 5 (atPC a 66016) t ∧
      t.pc=(if first.toNat < 128 then 66536 else 66036) ∧ HeaderInv t tail tag first ptr := by
    by_cases hf : first.toNat < 128
    · have hflag := (long_flag first).mpr hf
      refine ⟨?_,?trace,?post⟩
      case trace =>
        repeat parser_read_step
        exact .nil _
      case post => simp_all [HeaderInv,getReg_setReg]
    · have hflag := mt (long_flag first).mp hf
      simp only [BitVec.ofNat_eq_ofNat] at *
      refine ⟨?_,?trace,?post⟩
      case trace =>
        repeat parser_read_step
        exact .nil _
      case post => simp_all [HeaderInv,getReg_setReg]
  obtain ⟨t,ht,hpc',hout⟩ := hs
  exact ⟨t,by simpa using ha.append (readTrace_at_pc hpc ht),hpc',hout⟩

theorem missing_second (s : State) (tag : UInt8) (ptr : Word) (hi : TagInv s [tag] tag ptr) :
    ∃ t, ReadTrace decoder 0 [] 18 (atPC s 65936) t ∧ t.pc=0 ∧ ErrorOutput 1 t := by
  rcases hi with ⟨htag,hptr,hlen,hra,hread⟩
  have hprefix : ∃ a, ReadTrace decoder 0 [] 2 (atPC s 65936) a ∧ a.pc=65944 ∧ a.getReg .x1=0 := by
    refine ⟨?_,?trace,?post⟩
    case trace =>
      repeat parser_read_step
      exact .nil _
    case post => simp [getReg_setReg,hra]
  obtain ⟨a,ha,hpc,hr⟩ := hprefix
  obtain ⟨t,ht,hret,hout,_⟩ := error_return 5 a hr
  exact ⟨t,by simpa using ha.append (readTrace_at_pc hpc ht),hret,hout⟩

end Libp2pAsm.Refinement.AsmDer
