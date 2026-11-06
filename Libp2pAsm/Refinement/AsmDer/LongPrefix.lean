import Libp2pAsm.Refinement.AsmDer.Header
import Libp2pAsm.Refinement.AsmDer.Result

namespace Libp2pAsm.Refinement.AsmDer
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def longCheck (first : UInt8) (available : Nat) : Except Spec.Codec.Der.Error Nat :=
  if first.toNat=128 then .error .indefinite
  else if first.toNat=255 then .error .reserved
  else if 8 < first.toNat%128 then .error .overflow
  else if available < first.toNat%128 then .error .truncated
  else .ok (first.toNat%128)

def LongOutcome (tail : List UInt8) (tag first : UInt8) (ptr : Word) (t : State) : Prop :=
  match longCheck first tail.length with
  | .error e => t.pc=0 ∧ DecodePost (.error e) t ∧ DecodeClear t
  | .ok count => t.pc=66340 ∧ HeaderInv t tail tag first ptr ∧
      t.getReg .x17=BitVec.ofNat 64 count

theorem long_prefix (s : State) (tail : List UInt8) (tag first : UInt8) (ptr : Word)
    (hl : tail.length < 2^64) (hi : HeaderInv s tail tag first ptr) :
    ∃ n t, n ≤ 24 ∧ ReadTrace decoder 0 [] n (atPC s 66036) t ∧ LongOutcome tail tag first ptr t := by
  rcases hi with ⟨htag,hfirst,hheader,hptr,hremain,hra,hread⟩
  have h128 : BitVec.ofNat 64 first.toNat=(128 : Word) ↔ first.toNat=128 := by
    simpa using word_byte_eq first 128 (by decide)
  have h255 : BitVec.ofNat 64 first.toNat=(255 : Word) ↔ first.toNat=255 := by
    simpa using word_byte_eq first 255 (by decide)
  have hpay := unsigned_payload_word first
  have hb : first.toNat%128 < 2^64 := by omega
  have hsmall : BitVec.ofNat 64 (first.toNat%128) ≤ (8 : Word) ↔ first.toNat%128 ≤ 8 := by
    simp [BitVec.le_def,Nat.mod_eq_of_lt hb]
  have hfits : BitVec.ofNat 64 (first.toNat%128) ≤ BitVec.ofNat 64 tail.length ↔ first.toNat%128 ≤ tail.length := by
    simp [BitVec.le_def,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt hl]
  by_cases h128n : first.toNat=128
  · have hp : ∃ a, ReadTrace decoder 0 [] 2 (atPC s 66036) a ∧ a.pc=66044 ∧ a.getReg .x1=0 := by
      refine ⟨?_,?trace,?post⟩
      case trace =>
        repeat parser_read_step
        exact .nil _
      case post => simp [getReg_setReg,hra]
    obtain ⟨a,ha,hpc,hr⟩ := hp
    obtain ⟨t,ht,hret,hout,_⟩ := error_return 6 a hr
    refine ⟨18,t,by decide,by simpa using ha.append (readTrace_at_pc hpc ht),?_⟩
    simpa only [LongOutcome,longCheck,if_pos h128n] using
      And.intro hret (And.intro (error_post t .indefinite hout) (error_clear t 7 hout))
  by_cases h255n : first.toNat=255
  · have hp : ∃ a, ReadTrace decoder 0 [] 4 (atPC s 66036) a ∧ a.pc=66120 ∧ a.getReg .x1=0 := by
      refine ⟨?_,?trace,?post⟩
      case trace =>
        repeat parser_read_step
        exact .nil _
      case post => simp [getReg_setReg,hra]
    obtain ⟨a,ha,hpc,hr⟩ := hp
    obtain ⟨t,ht,hret,hout,_⟩ := error_return 7 a hr
    refine ⟨20,t,by decide,by simpa using ha.append (readTrace_at_pc hpc ht),?_⟩
    simpa only [LongOutcome,longCheck,if_neg h128n,if_pos h255n] using
      And.intro hret (And.intro (error_post t .reserved hout) (error_clear t 8 hout))
  by_cases hc : 8 < first.toNat%128
  · have hsmall' : ¬BitVec.ofNat 64 (first.toNat%128) ≤ (8 : Word) := by rw [hsmall]; omega
    simp only [BitVec.ofNat_eq_ofNat] at *
    have hp : ∃ a, ReadTrace decoder 0 [] 7 (atPC s 66036) a ∧ a.pc=66200 ∧ a.getReg .x1=0 := by
      refine ⟨?_,?trace,?post⟩
      case trace =>
        repeat parser_read_step
        exact .nil _
      case post => simp [getReg_setReg,hra]
    obtain ⟨a,ha,hpc,hr⟩ := hp
    obtain ⟨t,ht,hret,hout,_⟩ := error_return 8 a hr
    refine ⟨23,t,by decide,by simpa using ha.append (readTrace_at_pc hpc ht),?_⟩
    simpa only [LongOutcome,longCheck,if_neg h128n,if_neg h255n,if_pos hc] using
      And.intro hret (And.intro (error_post t .overflow hout) (error_clear t 2 hout))
  have hsmall' : BitVec.ofNat 64 (first.toNat%128) ≤ (8 : Word) := hsmall.mpr (by omega)
  by_cases hf : tail.length < first.toNat%128
  · have hfits' : ¬BitVec.ofNat 64 (first.toNat%128) ≤ BitVec.ofNat 64 tail.length := by rw [hfits]; omega
    simp only [BitVec.ofNat_eq_ofNat] at *
    have hp : ∃ a, ReadTrace decoder 0 [] 8 (atPC s 66036) a ∧ a.pc=66272 ∧ a.getReg .x1=0 := by
      refine ⟨?_,?trace,?post⟩
      case trace =>
        repeat parser_read_step
        exact .nil _
      case post => simp [getReg_setReg,hra]
    obtain ⟨a,ha,hpc,hr⟩ := hp
    obtain ⟨t,ht,hret,hout,_⟩ := error_return 9 a hr
    refine ⟨24,t,by decide,by simpa using ha.append (readTrace_at_pc hpc ht),?_⟩
    simpa only [LongOutcome,longCheck,if_neg h128n,if_neg h255n,if_neg hc,if_pos hf] using
      And.intro hret (And.intro (error_post t .truncated hout) (error_clear t 1 hout))
  have hfits' := hfits.mpr (show first.toNat%128 ≤ tail.length by omega)
  simp only [BitVec.ofNat_eq_ofNat] at *
  refine ⟨8,?_,by decide,?trace,?post⟩
  case trace =>
    repeat parser_read_step
    exact .nil _
  case post =>
    simp only [LongOutcome,longCheck,if_neg h128n,if_neg h255n,if_neg hc,if_neg hf]
    simp_all [HeaderInv,getReg_setReg]

end Libp2pAsm.Refinement.AsmDer
