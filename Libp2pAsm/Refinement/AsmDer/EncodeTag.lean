import Libp2pAsm.Refinement.AsmDer.EncodeErrors
import Libp2pAsm.Refinement.AsmDer.EncodeCount
import Libp2pAsm.Refinement.AsmDer.Arithmetic

namespace Libp2pAsm.Refinement.AsmDer.Encode
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

theorem word_byte_repr (w : Word) (h : w.toNat<256) :
    w=BitVec.ofNat 64 w.toNat.toUInt8.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt h,Nat.mod_eq_of_lt w.isLt]

theorem tag_low_checks (s : State) (b : UInt8) (htag : s.getReg .x10=BitVec.ofNat 64 b.toNat)
    (hra : s.getReg .x1=0) :
    ∃ n t, n≤21 ∧ AccessTrace encoder 0 [] [] n (atPC s 65612) t ∧
      (if Spec.Codec.Der.supportedTag b.toNat then t.pc=65768 ∧ EncodeArgs s t
       else t.pc=0 ∧ ErrorOutput 6 t) := by
  have hlo := tag_low b
  have hzero := tag_zero b
  by_cases hh : b.toNat%32=31
  · have hmask : BitVec.ofNat 64 b.toNat &&& (31 : Word)=31 := by rw [hlo,hh]; rfl
    have hbad : Spec.Codec.Der.supportedTag b.toNat=false := by
      apply Bool.eq_false_iff.mpr; intro h; have := (tag_supported b).mp h; omega
    have hp : ∃ a, AccessTrace encoder 0 [] [] 3 (atPC s 65612) a ∧ a.pc=65624 ∧ a.getReg .x1=0 := by
      refine ⟨?_,?trace,?post⟩
      case trace =>
        repeat parser_access_step
        exact .nil _
      case post => simp [getReg_setReg,hra]
    obtain ⟨a,ha,hpc,hr⟩ := hp
    obtain ⟨t,ht,hret,ho,_⟩ := error_return 1 a hr
    exact ⟨19,t,by decide,by simpa using ha.append (accessTrace_at_pc hpc ht),by simpa only [hbad,Bool.false_eq_true,if_false,BitVec.ofNat_eq_ofNat] using And.intro hret (show ErrorOutput 6 t from ho)⟩
  have hmask : BitVec.ofNat 64 b.toNat &&& (31 : Word)≠31 := by
    rw [hlo]; intro he; have := congrArg BitVec.toNat he; simp at this; omega
  by_cases hz : b.toNat=0 ∨ b.toNat=32
  · have hmask0 := hzero.mpr hz
    have hbad : Spec.Codec.Der.supportedTag b.toNat=false := by
      apply Bool.eq_false_iff.mpr; intro h; have := (tag_supported b).mp h; omega
    simp only [BitVec.ofNat_eq_ofNat] at *
    have hp : ∃ a, AccessTrace encoder 0 [] [] 5 (atPC s 65612) a ∧ a.pc=65700 ∧ a.getReg .x1=0 := by
      refine ⟨?_,?trace,?post⟩
      case trace =>
        repeat parser_access_step
        exact .nil _
      case post => simp [getReg_setReg,hra]
    obtain ⟨a,ha,hpc,hr⟩ := hp
    obtain ⟨t,ht,hret,ho,_⟩ := error_return 2 a hr
    exact ⟨21,t,by decide,by simpa using ha.append (accessTrace_at_pc hpc ht),by simpa only [hbad,Bool.false_eq_true,if_false,BitVec.ofNat_eq_ofNat] using And.intro hret (show ErrorOutput 6 t from ho)⟩
  have hmask0 := mt hzero.mp hz
  have hgood := (tag_supported b).mpr (by omega)
  simp only [BitVec.ofNat_eq_ofNat] at *
  refine ⟨5,?_,by decide,?trace,?post⟩
  case trace =>
    repeat parser_access_step
    exact .nil _
  case post => simp [hgood,EncodeArgs,getReg_setReg]

theorem tag_checks (s : State) (hra : s.getReg .x1=0) :
    ∃ n t, n≤23 ∧ AccessTrace encoder 0 [] [] n (atPC s 65536) t ∧
      (if Spec.Codec.Der.supportedTag (s.getReg .x10).toNat then t.pc=65768 ∧ EncodeArgs s t
       else t.pc=0 ∧ ErrorOutput 6 t) := by
  by_cases hh : (s.getReg .x10).toNat<256
  · have hhigh := (word_shift_zero_iff (s.getReg .x10) 8).mpr hh
    have hp : ∃ a, AccessTrace encoder 0 [] [] 2 (atPC s 65536) a ∧ a.pc=65612 ∧ EncodeArgs s a := by
      refine ⟨?_,?trace,?post⟩
      case trace =>
        repeat parser_access_step
        exact .nil _
      case post => simp [EncodeArgs,getReg_setReg]
    obtain ⟨a,ha,hpc,hargs⟩ := hp
    have ha10 := hargs .x10 (by simp)
    have ha1 := (hargs .x1 (by simp)).trans hra
    obtain ⟨n,t,hn,ht,ho⟩ := tag_low_checks a (s.getReg .x10).toNat.toUInt8
      (ha10.trans (word_byte_repr _ hh)) ha1
    have hnat : (s.getReg .x10).toNat.toUInt8.toNat=(s.getReg .x10).toNat := by simp [Nat.mod_eq_of_lt hh]
    rw [hnat] at ho
    refine ⟨2+n,t,by omega,by simpa using ha.append (accessTrace_at_pc hpc ht),?_⟩
    by_cases hgood : Spec.Codec.Der.supportedTag (s.getReg .x10).toNat=true
    · simp only [if_pos hgood] at ho ⊢
      exact ⟨ho.1,hargs.trans ho.2⟩
    · simpa only [if_neg hgood] using ho
  · have hhigh : s.getReg .x10 >>> (8 : Nat)≠0 := mt (word_shift_zero_iff (s.getReg .x10) 8).mp hh
    have hbad : Spec.Codec.Der.supportedTag (s.getReg .x10).toNat=false := by
      simp [Spec.Codec.Der.supportedTag,hh]
    simp only [BitVec.ofNat_eq_ofNat] at *
    have hp : ∃ a, AccessTrace encoder 0 [] [] 2 (atPC s 65536) a ∧ a.pc=65544 ∧ a.getReg .x1=0 := by
      refine ⟨?_,?trace,?post⟩
      case trace =>
        repeat parser_access_step
        exact .nil _
      case post => simp [getReg_setReg,hra]
    obtain ⟨a,ha,hpc,hr⟩ := hp
    obtain ⟨t,ht,hret,ho,_⟩ := error_return 0 a hr
    exact ⟨18,t,by decide,by simpa using ha.append (accessTrace_at_pc hpc ht),by simpa only [hbad,Bool.false_eq_true,if_false,BitVec.ofNat_eq_ofNat] using And.intro hret (show ErrorOutput 6 t from ho)⟩

end Libp2pAsm.Refinement.AsmDer.Encode
