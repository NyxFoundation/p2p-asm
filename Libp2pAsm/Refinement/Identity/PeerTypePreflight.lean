import Libp2pAsm.Refinement.Identity.PeerTypes

namespace Libp2pAsm.Refinement.Identity.Peer
open Rv64 Rv64.Logic Rv64.Logic.Parser

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def typeError (kind length cap : Word) : Option Spec.Identity.PublicKey.Error :=
  if kind=1 ∨ kind=2 then
    if length=kind+31 then if length+6≤cap then none else some .capacity
    else some .keyLength
  else some .keyType

theorem typeError_none (kind length cap : Word) (h : typeError kind length cap=none) :
    (kind=1 ∨ kind=2) ∧ length=kind+31 ∧ length+6≤cap := by
  unfold typeError at h
  repeat' (split at h <;> try cases h)
  simp_all

theorem validated_lengths (kind length cap : Word) (h : typeError kind length cap=none) :
    (length=32 ∧ length+6=38) ∨ (length=33 ∧ length+6=39) := by
  obtain ⟨hk,hl,_⟩ := typeError_none kind length cap h
  rcases hk with rfl | rfl <;> subst length <;> simp

theorem type_preflight (s : State) (hra : s.getReg .x1=0) :
    ∃ n t, n≤56 ∧ AccessTrace program 0 [] [] n (atPC s 65536) t ∧
      (match typeError (s.getReg .x10) (s.getReg .x12) (s.getReg .x14) with
      | some e => t.pc=0 ∧ ErrorOutput e.code t
      | none => t.pc=65776 ∧ Args s t ∧ t.getReg .x29=s.getReg .x12+6) := by
  obtain ⟨nk,a,hnk,ha,hak⟩ := kind_check s hra
  by_cases hk : s.getReg .x10=1 ∨ s.getReg .x10=2
  · simp only [if_pos hk] at hak
    have ha1 := (hak.2 .x1 (by simp)).trans hra
    obtain ⟨nl,b,hnl,hb,hbl⟩ := length_check a ha1
    have ha10 := hak.2 .x10 (by simp)
    have ha12 := hak.2 .x12 (by simp)
    rw [ha10,ha12] at hbl
    by_cases hl : s.getReg .x12=s.getReg .x10+31
    · simp only [if_pos hl] at hbl
      have hargs := hak.2.trans hbl.2
      have hb1 := (hargs .x1 (by simp)).trans hra
      obtain ⟨nc,t,hnc,ht,htc⟩ := capacity_check b hb1
      have hb12 := hargs .x12 (by simp)
      have hb14 := hargs .x14 (by simp)
      rw [hb12,hb14] at htc
      refine ⟨nk+nl+nc,t,by omega,by simpa using ((ha.append (accessTrace_at_pc hak.1 hb)).append
        (accessTrace_at_pc hbl.1 ht)),?_⟩
      by_cases hc : s.getReg .x12+6≤s.getReg .x14
      · simp only [if_pos hc] at htc
        simpa only [typeError,if_pos hk,if_pos hl,if_pos hc] using
          And.intro htc.1 (And.intro (hargs.trans htc.2.1) htc.2.2)
      · simp only [if_neg hc] at htc
        simpa only [typeError,if_pos hk,if_pos hl,if_neg hc,Spec.Identity.PublicKey.Error.code] using htc
    · simp only [if_neg hl] at hbl
      exact ⟨nk+nl,b,by omega,by simpa using ha.append (accessTrace_at_pc hak.1 hb),
        by simpa only [typeError,if_pos hk,if_neg hl,Spec.Identity.PublicKey.Error.code] using hbl⟩
  · simp only [if_neg hk] at hak
    exact ⟨nk,a,by omega,ha,by simpa only [typeError,if_neg hk,Spec.Identity.PublicKey.Error.code] using hak⟩

end Libp2pAsm.Refinement.Identity.Peer
