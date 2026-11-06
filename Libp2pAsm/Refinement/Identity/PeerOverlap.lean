import Libp2pAsm.Refinement.Identity.PeerKeyRange
import Libp2pAsm.Refinement.Identity.PeerOutputRange

namespace Libp2pAsm.Refinement.Identity.Peer
open Rv64 Rv64.Logic Rv64.Logic.Parser

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

theorem nonzero_toNat (w : Word) (h : w≠0) : 0<w.toNat := by
  have hn : w.toNat≠0 := by intro he; apply h; apply BitVec.eq_of_toNat_eq; exact he
  omega

theorem overlap_check (s : State) (hk : s.getReg .x12≠0) (ho : s.getReg .x29≠0) (hra : s.getReg .x1=0) :
    ∃ n t, n≤21 ∧ AccessTrace program 0 [] [] n (atPC s 65960) t ∧
      (if DisjointSpans (s.getReg .x11) (s.getReg .x12).toNat (s.getReg .x13) (s.getReg .x29).toNat then
        t.pc=66136 ∧ Args s t ∧ t.getReg .x29=s.getReg .x29 else t.pc=0 ∧ ErrorOutput 4 t) := by
  have hkpos := nonzero_toNat _ hk
  have hopos := nonzero_toNat _ ho
  by_cases hside : s.getReg .x13≤s.getReg .x11
  · have hsideNat : (s.getReg .x13).toNat≤(s.getReg .x11).toNat := hside
    have heq : DisjointSpans (s.getReg .x11) (s.getReg .x12).toNat (s.getReg .x13) (s.getReg .x29).toNat ↔
        s.getReg .x29≤s.getReg .x11-s.getReg .x13 := by
      rw [difference_fits _ _ _ hside]; unfold DisjointSpans; omega
    by_cases hfit : s.getReg .x29≤s.getReg .x11-s.getReg .x13
    · have hsep := heq.mpr hfit
      refine ⟨5,?_,by decide,?trace,?post⟩
      case trace =>
        repeat parser_access_step
        exact .nil _
      case post => simp [hsep,Args,getReg_setReg]
    · have hsep := mt heq.mp hfit
      simp only [BitVec.ofNat_eq_ofNat] at *
      have hp : ∃ a, AccessTrace program 0 [] [] 5 (atPC s 65960) a ∧ a.pc=66068 ∧ a.getReg .x1=0 := by
        refine ⟨?_,?trace,?post⟩
        case trace =>
          repeat parser_access_step
          exact .nil _
        case post => simp [getReg_setReg,hra]
      obtain ⟨a,ha,hpc,hr⟩ := hp
      obtain ⟨t,ht,hret,hout,_⟩ := error_return 6 a hr
      exact ⟨21,t,by decide,by simpa using ha.append (accessTrace_at_pc hpc ht),
        by simpa only [if_neg hsep,BitVec.ofNat_eq_ofNat] using And.intro hret (show ErrorOutput 4 t from hout)⟩
  · have hsideNat : (s.getReg .x11).toNat<(s.getReg .x13).toNat := by
      rw [BitVec.le_def] at hside; omega
    have hle : s.getReg .x11≤s.getReg .x13 := by rw [BitVec.le_def]; omega
    have heq : DisjointSpans (s.getReg .x11) (s.getReg .x12).toNat (s.getReg .x13) (s.getReg .x29).toNat ↔
        s.getReg .x12≤s.getReg .x13-s.getReg .x11 := by
      rw [difference_fits _ _ _ hle]; unfold DisjointSpans; omega
    by_cases hfit : s.getReg .x12≤s.getReg .x13-s.getReg .x11
    · have hsep := heq.mpr hfit
      simp only [BitVec.ofNat_eq_ofNat] at *
      refine ⟨6,?_,by decide,?trace,?post⟩
      case trace =>
        repeat parser_access_step
        exact .nil _
      case post => simp [hsep,Args,getReg_setReg]
    · have hsep := mt heq.mp hfit
      simp only [BitVec.ofNat_eq_ofNat] at *
      have hp : ∃ a, AccessTrace program 0 [] [] 5 (atPC s 65960) a ∧ a.pc=65988 ∧ a.getReg .x1=0 := by
        refine ⟨?_,?trace,?post⟩
        case trace =>
          repeat parser_access_step
          exact .nil _
        case post => simp [getReg_setReg,hra]
      obtain ⟨a,ha,hpc,hr⟩ := hp
      obtain ⟨t,ht,hret,hout,_⟩ := error_return 5 a hr
      exact ⟨21,t,by decide,by simpa using ha.append (accessTrace_at_pc hpc ht),
        by simpa only [if_neg hsep,BitVec.ofNat_eq_ofNat] using And.intro hret (show ErrorOutput 4 t from hout)⟩

end Libp2pAsm.Refinement.Identity.Peer
