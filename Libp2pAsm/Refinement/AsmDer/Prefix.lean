import Libp2pAsm.Refinement.AsmDer.Arithmetic
import Libp2pAsm.Refinement.AsmDer.Errors

namespace Libp2pAsm.Refinement.AsmDer
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def TagInv (s : State) (bytes : List UInt8) (tag : UInt8) (ptr : Word) : Prop :=
  s.getReg .x12=BitVec.ofNat 64 tag.toNat ∧ s.getReg .x10=ptr ∧
    s.getReg .x11=BitVec.ofNat 64 bytes.length ∧ s.getReg .x1=0 ∧ Reads s.memory ptr bytes

theorem take_tag (s : State) (b : UInt8) (bs : List UInt8)
    (hl : (b::bs).length < 2^64) (hlen : s.getReg .x11=BitVec.ofNat 64 (b::bs).length)
    (hra : s.getReg .x1=0) (hm : Reads s.memory (s.getReg .x10) (b::bs)) :
    ∃ t, ReadTrace decoder 0 [(1,s.getReg .x10)] 4 (atPC s 65628) t ∧ t.pc=65780 ∧
      TagInv t (b::bs) b (s.getReg .x10) := by
  have hn : s.getReg .x11 ≠ 0 := by rw [hlen]; exact word_length_nonzero _ hl (by simp)
  have hbyte := hm.head
  have hhigh := byte_high_zero b
  refine ⟨?_,?trace,?post⟩
  case trace =>
    repeat parser_read_step
    exact .nil _
  case post => simp_all [TagInv,getReg_setReg]

theorem tag_pass (s : State) (bytes : List UInt8) (tag : UInt8) (ptr : Word)
    (hi : TagInv s bytes tag ptr) (ht : Spec.Codec.Der.supportedTag tag.toNat=true) :
    ∃ t, ReadTrace decoder 0 [] 5 (atPC s 65780) t ∧ t.pc=65936 ∧ TagInv t bytes tag ptr := by
  rcases hi with ⟨htag,hptr,hlen,hra,hread⟩
  obtain ⟨hlo,hzero,hthirty⟩ := (tag_supported tag).mp ht
  have hlow : BitVec.ofNat 64 tag.toNat &&& (31 : Word) ≠ 31 := by
    rw [tag_low]; intro he
    have hv := congrArg BitVec.toNat he
    simp at hv; omega
  have hmask : BitVec.ofNat 64 tag.toNat &&& (18446744073709551583 : Word)≠0 := by
    intro he; have := (tag_zero tag).mp he; omega
  simp only [BitVec.ofNat_eq_ofNat] at *
  refine ⟨?_,?trace,?post⟩
  case trace =>
    repeat parser_read_step
    exact .nil _
  case post => simp_all [TagInv,getReg_setReg]

theorem tag_high_error (s : State) (bytes : List UInt8) (tag : UInt8) (ptr : Word)
    (hi : TagInv s bytes tag ptr) (ht : tag.toNat%32=31) :
    ∃ t, ReadTrace decoder 0 [] 19 (atPC s 65780) t ∧ t.pc=0 ∧ ErrorOutput 6 t := by
  rcases hi with ⟨htag,hptr,hlen,hra,hread⟩
  have hlow : BitVec.ofNat 64 tag.toNat &&& (31 : Word)=31 := by rw [tag_low,ht]; rfl
  have hprefix : ∃ a, ReadTrace decoder 0 [] 3 (atPC s 65780) a ∧ a.pc=65792 ∧ a.getReg .x1=0 := by
    refine ⟨?_,?trace,?post⟩
    case trace =>
      repeat parser_read_step
      exact .nil _
    case post => simp [getReg_setReg,hra]
  obtain ⟨a,ha,hpc,hr⟩ := hprefix
  obtain ⟨t,ht,hret,hout,_⟩ := error_return 3 a hr
  exact ⟨t,by simpa using ha.append (readTrace_at_pc hpc ht),hret,hout⟩

theorem tag_zero_error (s : State) (bytes : List UInt8) (tag : UInt8) (ptr : Word)
    (hi : TagInv s bytes tag ptr) (ht : tag.toNat=0 ∨ tag.toNat=32) :
    ∃ t, ReadTrace decoder 0 [] 21 (atPC s 65780) t ∧ t.pc=0 ∧ ErrorOutput 6 t := by
  rcases hi with ⟨htag,hptr,hlen,hra,hread⟩
  have hlo : tag.toNat%32=0 := by rcases ht with h | h <;> simp [h]
  have hlow : BitVec.ofNat 64 tag.toNat &&& (31 : Word)=0 := by rw [tag_low,hlo]; rfl
  have hmask := (tag_zero tag).mpr ht
  simp only [BitVec.ofNat_eq_ofNat] at *
  have hprefix : ∃ a, ReadTrace decoder 0 [] 5 (atPC s 65780) a ∧ a.pc=65868 ∧ a.getReg .x1=0 := by
    refine ⟨?_,?trace,?post⟩
    case trace =>
      repeat parser_read_step
      exact .nil _
    case post => simp [getReg_setReg,hra]
  obtain ⟨a,ha,hpc,hr⟩ := hprefix
  obtain ⟨t,ht,hret,hout,_⟩ := error_return 4 a hr
  exact ⟨t,by simpa using ha.append (readTrace_at_pc hpc ht),hret,hout⟩

end Libp2pAsm.Refinement.AsmDer
