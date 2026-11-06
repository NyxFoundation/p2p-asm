import Libp2pAsm.Refinement.Identity.PeerErrors
import Libp2pAsm.Rv64.Logic.ParserDisjoint

namespace Libp2pAsm.Refinement.Identity.Peer
open Rv64 Rv64.Logic Rv64.Logic.Parser

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def Args (s t : State) : Prop := ∀ r∈[Reg.x1,.x10,.x11,.x12,.x13,.x14],t.getReg r=s.getReg r

theorem Args.trans {s t u : State} (h : Args s t) (g : Args t u) : Args s u :=
  fun r hr => (g r hr).trans (h r hr)

/-- The complete 64-bit enum is compared; no conversion to uint32 occurs. -/
theorem kind_exact (w : Word) : (w=1 ∨ w=2) ↔ (w.toNat=1 ∨ w.toNat=2) := by
  constructor
  · rintro (rfl | rfl) <;> simp
  · rintro (h | h)
    · left; apply BitVec.eq_of_toNat_eq; exact h
    · right; apply BitVec.eq_of_toNat_eq; exact h

theorem kind_check (s : State) (hra : s.getReg .x1=0) :
    ∃ n t, n≤20 ∧ AccessTrace program 0 [] [] n (atPC s 65536) t ∧
      (if s.getReg .x10=1 ∨ s.getReg .x10=2 then t.pc=65624 ∧ Args s t else t.pc=0 ∧ ErrorOutput 8 t) := by
  by_cases h1 : s.getReg .x10=1
  · refine ⟨2,?_,by decide,?trace,?post⟩
    case trace =>
      repeat parser_access_step
      exact .nil _
    case post => simp [h1,Args,getReg_setReg]
  by_cases h2 : s.getReg .x10=2
  · simp only [BitVec.ofNat_eq_ofNat] at *
    refine ⟨5,?_,by decide,?trace,?post⟩
    case trace =>
      repeat parser_access_step
      exact .nil _
    case post => simp [h2,Args,getReg_setReg]
  simp only [BitVec.ofNat_eq_ofNat] at *
  have hp : ∃ a, AccessTrace program 0 [] [] 4 (atPC s 65536) a ∧ a.pc=65552 ∧ a.getReg .x1=0 := by
    refine ⟨?_,?trace,?post⟩
    case trace =>
      repeat parser_access_step
      exact .nil _
    case post => simp [getReg_setReg,hra]
  obtain ⟨a,ha,hpc,hr⟩ := hp
  obtain ⟨t,ht,hret,ho,_⟩ := error_return 0 a hr
  refine ⟨20,t,by decide,by simpa using ha.append (accessTrace_at_pc hpc ht),?_⟩
  simp only [h1,h2,or_self,if_false]
  exact ⟨hret,ho⟩

theorem length_check (s : State) (hra : s.getReg .x1=0) :
    ∃ n t, n≤18 ∧ AccessTrace program 0 [] [] n (atPC s 65624) t ∧
      (if s.getReg .x12=s.getReg .x10+31 then t.pc=65700 ∧ Args s t else t.pc=0 ∧ ErrorOutput 9 t) := by
  by_cases hl : s.getReg .x12=s.getReg .x10+31
  · refine ⟨2,?_,by decide,?trace,?post⟩
    case trace =>
      repeat parser_access_step
      exact .nil _
    case post => simp only [BitVec.ofNat_eq_ofNat] at hl; simp [hl,Args,getReg_setReg]
  simp only [BitVec.ofNat_eq_ofNat] at *
  have hp : ∃ a, AccessTrace program 0 [] [] 2 (atPC s 65624) a ∧ a.pc=65632 ∧ a.getReg .x1=0 := by
    refine ⟨?_,?trace,?post⟩
    case trace =>
      repeat parser_access_step
      exact .nil _
    case post => simp [getReg_setReg,hra]
  obtain ⟨a,ha,hpc,hr⟩ := hp
  obtain ⟨t,ht,hret,ho,_⟩ := error_return 1 a hr
  exact ⟨18,t,by decide,by simpa using ha.append (accessTrace_at_pc hpc ht),by simpa only [if_neg hl,BitVec.ofNat_eq_ofNat] using And.intro hret (show ErrorOutput 9 t from ho)⟩

theorem capacity_check (s : State) (hra : s.getReg .x1=0) :
    ∃ n t, n≤18 ∧ AccessTrace program 0 [] [] n (atPC s 65700) t ∧
      (if s.getReg .x12+6≤s.getReg .x14 then t.pc=65776 ∧ Args s t ∧ t.getReg .x29=s.getReg .x12+6
       else t.pc=0 ∧ ErrorOutput 5 t) := by
  by_cases hc : s.getReg .x12+6≤s.getReg .x14
  · refine ⟨2,?_,by decide,?trace,?post⟩
    case trace =>
      repeat parser_access_step
      exact .nil _
    case post => simp only [BitVec.ofNat_eq_ofNat] at hc; simp [hc,Args,getReg_setReg]
  simp only [BitVec.ofNat_eq_ofNat] at *
  have hp : ∃ a, AccessTrace program 0 [] [] 2 (atPC s 65700) a ∧ a.pc=65708 ∧ a.getReg .x1=0 := by
    refine ⟨?_,?trace,?post⟩
    case trace =>
      repeat parser_access_step
      exact .nil _
    case post => simp [getReg_setReg,hra]
  obtain ⟨a,ha,hpc,hr⟩ := hp
  obtain ⟨t,ht,hret,ho,_⟩ := error_return 2 a hr
  exact ⟨18,t,by decide,by simpa using ha.append (accessTrace_at_pc hpc ht),by simpa only [if_neg hc,BitVec.ofNat_eq_ofNat] using And.intro hret (show ErrorOutput 5 t from ho)⟩

end Libp2pAsm.Refinement.Identity.Peer
