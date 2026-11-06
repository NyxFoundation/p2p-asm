import Libp2pAsm.Refinement.Identity.PeerOverlap

namespace Libp2pAsm.Refinement.Identity.Peer
open Rv64 Rv64.Logic Rv64.Logic.Parser

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def rangesValid (key len out written : Word) : Prop :=
  key.toNat+len.toNat≤2^64 ∧ out.toNat+written.toNat≤2^64 ∧ DisjointSpans key len.toNat out written.toNat

instance (key len out written : Word) : Decidable (rangesValid key len out written) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ DisjointSpans key len.toNat out written.toNat))

theorem range_preflight (s : State) (hk : s.getReg .x12≠0) (ho : s.getReg .x29≠0) (hra : s.getReg .x1=0) :
    ∃ n t, n≤63 ∧ AccessTrace program 0 [] [] n (atPC s 65776) t ∧
      (if rangesValid (s.getReg .x11) (s.getReg .x12) (s.getReg .x13) (s.getReg .x29) then
        t.pc=66136 ∧ Args s t ∧ t.getReg .x29=s.getReg .x29 else t.pc=0 ∧ ErrorOutput 4 t) := by
  obtain ⟨nk,a,hnk,ha,hao⟩ := key_range s hk hra
  by_cases hs : (s.getReg .x11).toNat+(s.getReg .x12).toNat≤2^64
  · simp only [if_pos hs] at hao
    have ha13 := hao.2.1 .x13 (by simp)
    have ha29 := hao.2.2
    obtain ⟨no,b,hno,hb,hbo⟩ := output_range a (by rwa [ha29]) ((hao.2.1 .x1 (by simp)).trans hra)
    rw [ha13,ha29] at hbo
    by_cases hs' : (s.getReg .x13).toNat+(s.getReg .x29).toNat≤2^64
    · simp only [if_pos hs'] at hbo
      have hargs := hao.2.1.trans hbo.2.1
      have hb29 := hbo.2.2
      have hb11 := hargs .x11 (by simp)
      have hb12 := hargs .x12 (by simp)
      have hb13 := hargs .x13 (by simp)
      obtain ⟨nd,t,hnd,ht,hto⟩ := overlap_check b (by rwa [hb12]) (by rwa [hb29]) ((hargs .x1 (by simp)).trans hra)
      rw [hb11,hb12,hb13,hb29] at hto
      refine ⟨nk+no+nd,t,by omega,by simpa using ((ha.append (accessTrace_at_pc hao.1 hb)).append
        (accessTrace_at_pc hbo.1 ht)),?_⟩
      by_cases hd : DisjointSpans (s.getReg .x11) (s.getReg .x12).toNat (s.getReg .x13) (s.getReg .x29).toNat
      · simp only [if_pos hd] at hto
        simpa only [rangesValid,hs,hs',hd,and_self,if_true] using
          And.intro hto.1 (And.intro (hargs.trans hto.2.1) hto.2.2)
      · simp only [if_neg hd] at hto
        simpa only [rangesValid,hs,hs',hd,and_false,if_false] using hto
    · simp only [if_neg hs'] at hbo
      exact ⟨nk+no,b,by omega,by simpa using ha.append (accessTrace_at_pc hao.1 hb),
        by simpa [rangesValid,hs'] using hbo⟩
  · simp only [if_neg hs] at hao
    exact ⟨nk,a,by omega,ha,by simpa [rangesValid,hs] using hao⟩

end Libp2pAsm.Refinement.Identity.Peer
