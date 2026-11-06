import Libp2pAsm.Refinement.AsmDer.LongPrefix

namespace Libp2pAsm.Refinement.AsmDer
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

theorem natural_sub_word (a b : Nat) (h : b ≤ a) :
    BitVec.ofNat 64 a-BitVec.ofNat 64 b=BitVec.ofNat 64 (a-b) := by
  calc
    _ = (BitVec.ofNat 64 (a-b)+BitVec.ofNat 64 b)-BitVec.ofNat 64 b := by
      rw [←BitVec.ofNat_add,Nat.sub_add_cancel h]
    _ = _ := BitVec.add_sub_cancel _ _

theorem leading_zero (s : State) (bs : List UInt8) (tag first : UInt8) (ptr : Word)
    (hi : HeaderInv s (0::bs) tag first ptr) :
    ∃ t, ReadTrace decoder 0 [(1,ptr+2)] 18 (atPC s 66340) t ∧
      t.pc=0 ∧ DecodePost (.error .nonMinimal) t ∧ DecodeClear t := by
  rcases hi with ⟨htag,hfirst,hh,hptr,hr,hra,hread⟩
  have hbyte := hread.head
  have hp : ∃ a, ReadTrace decoder 0 [(1,ptr+2)] 2 (atPC s 66340) a ∧
      a.pc=66348 ∧ a.getReg .x1=0 := by
    refine ⟨?_,?trace,?post⟩
    case trace =>
      repeat parser_read_step
      exact .nil _
    case post => simp [getReg_setReg,hra]
  obtain ⟨a,ha,hpc,hra'⟩ := hp
  obtain ⟨t,ht,hret,hout,_⟩ := error_return 10 a hra'
  exact ⟨t,by simpa using ha.append (readTrace_at_pc hpc ht),hret,
    error_post t .nonMinimal hout,error_clear t 3 hout⟩

theorem leading_nonzero (s : State) (b : UInt8) (bs : List UInt8) (tag first : UInt8)
    (ptr : Word) (count : Nat) (hb : b≠0) (hc : count ≤ (b::bs).length)
    (hi : HeaderInv s (b::bs) tag first ptr) (hn : s.getReg .x17=BitVec.ofNat 64 count) :
    ∃ t, ReadTrace decoder 0 [(1,ptr+2)] 5 (atPC s 66340) t ∧ t.pc=66428 ∧
      LengthInv t ((b::bs).take count) 0 (BitVec.ofNat 64 tag.toNat)
        (BitVec.ofNat 64 (2+count)) (BitVec.ofNat 64 ((b::bs).length-count)) ∧
      t.getReg .x15=ptr+2 := by
  rcases hi with ⟨htag,hfirst,hh,hptr,hr,hra,hread⟩
  have hbyte := hread.head
  have hbn : b.toNat≠0 := by intro he; exact hb (UInt8.toNat_inj.mp he)
  have hbw : BitVec.ofNat 64 b.toNat≠(0 : Word) := by
    exact mt (word_byte_eq b 0 (by decide)).mp hbn
  have hsub := natural_sub_word (b::bs).length count hc
  have htake : ((b::bs).take count).length=count := by rw [List.length_take,Nat.min_eq_left hc]
  refine ⟨?_,?trace,?post⟩
  case trace =>
    repeat parser_read_step
    exact .nil _
  case post =>
    simp [LengthInv,getReg_setReg,htag,hptr,hn,hra,htake,BitVec.ofNat_add,hr,hsub]
    exact hread.take count

theorem late_minimal (s : State) (tag : UInt8) (header length remaining : Nat)
    (hl : length < 2^64) (hr : remaining < 2^64)
    (htag : s.getReg .x12=BitVec.ofNat 64 tag.toNat)
    (hh : s.getReg .x14=BitVec.ofNat 64 header)
    (hlen : s.getReg .x13=BitVec.ofNat 64 length)
    (hrem : s.getReg .x16=BitVec.ofNat 64 remaining) (hra : s.getReg .x1=0) :
    ∃ n t, n ≤ 20 ∧ ReadTrace decoder 0 [] n (atPC s 66456) t ∧ t.pc=0 ∧
      DecodePost (if length < 128 then .error .nonMinimal else
        if remaining < length then .error .truncated else .ok ⟨tag,header,length,header+length⟩) t ∧
      DecodeClear t := by
  have hg : (128 : Word) ≤ s.getReg .x13 ↔ 128 ≤ length := by
    rw [hlen,BitVec.le_def]; simp [Nat.mod_eq_of_lt hl]
  by_cases hb : length < 128
  · have hguard : ¬(128 : Word) ≤ s.getReg .x13 := by rw [hg]; omega
    have hp : ∃ a, ReadTrace decoder 0 [] 2 (atPC s 66456) a ∧ a.pc=66464 ∧ a.getReg .x1=0 := by
      refine ⟨?_,?trace,?post⟩
      case trace =>
        repeat parser_read_step
        exact .nil _
      case post => simp [getReg_setReg,hra]
    obtain ⟨a,ha,hpc,hra'⟩ := hp
    obtain ⟨t,ht,hret,hout,_⟩ := error_return 11 a hra'
    exact ⟨18,t,by decide,by simpa using ha.append (readTrace_at_pc hpc ht),hret,
      by simpa [hb] using error_post t .nonMinimal hout,error_clear t 3 hout⟩
  · have hguard := hg.mpr (show 128 ≤ length by omega)
    have hp : ∃ a, ReadTrace decoder 0 [] 3 (atPC s 66456) a ∧ a.pc=66536 ∧
        a.getReg .x12=BitVec.ofNat 64 tag.toNat ∧ a.getReg .x14=BitVec.ofNat 64 header ∧
        a.getReg .x13=BitVec.ofNat 64 length ∧ a.getReg .x16=BitVec.ofNat 64 remaining ∧ a.getReg .x1=0 := by
      refine ⟨?_,?trace,?post⟩
      case trace =>
        repeat parser_read_step
        exact .nil _
      case post => simp [getReg_setReg,htag,hh,hlen,hrem,hra]
    obtain ⟨a,ha,hpc,ha12,ha14,ha13,ha16,ha1⟩ := hp
    obtain ⟨n,t,hn,ht,hret,hpost,hclear⟩ := content_result a tag header length remaining hl hr ha12 ha14 ha13 ha16 ha1
    exact ⟨3+n,t,by omega,by simpa using ha.append (readTrace_at_pc hpc ht),hret,
      by simpa [hb] using hpost,hclear⟩

end Libp2pAsm.Refinement.AsmDer
