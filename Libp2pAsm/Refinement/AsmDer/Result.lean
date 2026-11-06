import Libp2pAsm.Refinement.AsmDer.Errors

namespace Libp2pAsm.Refinement.AsmDer
open Rv64 Rv64.Logic Rv64.Logic.Parser

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def DecodeClear (s : State) : Prop :=
  ∀ r ∈ Asm.Crypto.Sha2.cleared, r ∉ [.x10,.x11,.x12,.x13,.x14] → s.getReg r=0

theorem error_clear (s : State) (status : Nat) (h : ErrorOutput status s) : DecodeClear s := by
  intro r hr hout
  exact h.2 r hr (by intro he; subst r; simp at hout)

theorem content_result (s : State) (tag : UInt8) (header length remaining : Nat)
    (hl : length < 2^64) (hr : remaining < 2^64)
    (htag : s.getReg .x12=BitVec.ofNat 64 tag.toNat)
    (hheader : s.getReg .x14=BitVec.ofNat 64 header)
    (hlength : s.getReg .x13=BitVec.ofNat 64 length)
    (hremain : s.getReg .x16=BitVec.ofNat 64 remaining) (hra : s.getReg .x1=0) :
    ∃ n t, n ≤ 17 ∧ ReadTrace decoder 0 [] n (atPC s 66536) t ∧ t.pc=0 ∧
      DecodePost (if remaining < length then .error .truncated else
        .ok ⟨tag,header,length,header+length⟩) t ∧ DecodeClear t := by
  have hguard : s.getReg .x13 ≤ s.getReg .x16 ↔ length ≤ remaining := by
    rw [hlength,hremain,BitVec.le_def]
    simp [Nat.mod_eq_of_lt hl,Nat.mod_eq_of_lt hr]
  by_cases hb : length ≤ remaining
  · have hg := hguard.mpr hb
    refine ⟨16,?_,by decide,?trace,?post⟩
    case trace =>
      repeat parser_read_step
      exact .nil _
    case post =>
      simp [show ¬remaining < length by omega,DecodePost,DecodeClear,
        Asm.Crypto.Sha2.cleared,getReg_setReg,BitVec.ofNat_add,hlength]
  · have hg := mt hguard.mp hb
    simp only [BitVec.ofNat_eq_ofNat] at *
    have hp : ∃ a, ReadTrace decoder 0 [] 1 (atPC s 66536) a ∧ a.pc=66540 ∧ a.getReg .x1=0 := by
      refine ⟨?_,?trace,?post⟩
      case trace =>
        parser_read_step
        exact .nil _
      case post => simp [getReg_setReg,hra]
    obtain ⟨a,ha,hpc,hra'⟩ := hp
    obtain ⟨t,ht,hret,hout,_⟩ := error_return 12 a hra'
    refine ⟨17,t,by decide,by simpa using ha.append (readTrace_at_pc hpc ht),hret,?_,error_clear t 1 hout⟩
    simpa only [if_pos (show remaining < length by omega)] using error_post t .truncated hout

end Libp2pAsm.Refinement.AsmDer
