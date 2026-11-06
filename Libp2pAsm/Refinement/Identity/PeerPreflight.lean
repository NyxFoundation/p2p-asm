import Libp2pAsm.Refinement.Identity.PeerTypePreflight
import Libp2pAsm.Refinement.Identity.PeerRangePreflight

namespace Libp2pAsm.Refinement.Identity.Peer
open Rv64 Rv64.Logic Rv64.Logic.Parser

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def rawError (kind key length out cap : Word) : Option Spec.Identity.PublicKey.Error :=
  match typeError kind length cap with
  | some e => some e
  | none => if rangesValid key length out (length+6) then none else some .range

theorem preflight (s : State) (hra : s.getReg .x1=0) :
    ∃ n t, n≤119 ∧ AccessTrace program 0 [] [] n (atPC s 65536) t ∧
      (match rawError (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13) (s.getReg .x14) with
      | some e => t.pc=0 ∧ ErrorOutput e.code t
      | none => t.pc=66136 ∧ Args s t ∧ t.getReg .x29=s.getReg .x12+6) := by
  obtain ⟨nt,a,hnt,ha,hao⟩ := type_preflight s hra
  cases he : typeError (s.getReg .x10) (s.getReg .x12) (s.getReg .x14) with
  | some e =>
    simp only [he] at hao
    exact ⟨nt,a,by omega,ha,by simpa only [rawError,he] using hao⟩
  | none =>
    simp only [he] at hao
    have hlengths := validated_lengths _ _ _ he
    have ha11 := hao.2.1 .x11 (by simp)
    have ha12 := hao.2.1 .x12 (by simp)
    have ha13 := hao.2.1 .x13 (by simp)
    have ha29 := hao.2.2
    have hk : a.getReg .x12≠0 := by rw [ha12]; rcases hlengths with h | h <;> rw [h.1] <;> decide
    have hw : a.getReg .x29≠0 := by rw [ha29]; rcases hlengths with h | h <;> rw [h.2] <;> decide
    obtain ⟨nr,t,hnr,ht,hto⟩ := range_preflight a hk hw ((hao.2.1 .x1 (by simp)).trans hra)
    rw [ha11,ha12,ha13,ha29] at hto
    refine ⟨nt+nr,t,by omega,by simpa using ha.append (accessTrace_at_pc hao.1 ht),?_⟩
    unfold rawError
    simp only [he]
    by_cases hv : rangesValid (s.getReg .x11) (s.getReg .x12) (s.getReg .x13) (s.getReg .x12+6)
    · simp only [if_pos hv] at hto ⊢
      exact ⟨hto.1,hao.2.1.trans hto.2.1,hto.2.2⟩
    · simp only [if_neg hv] at hto ⊢
      exact hto

theorem validated (kind key length out cap : Word) (h : rawError kind key length out cap=none) :
    (kind.toNat=1 ∨ kind.toNat=2) ∧ length.toNat=31+kind.toNat ∧
      (length+6).toNat=length.toNat+6 ∧ length.toNat+6≤cap.toNat ∧
      key.toNat+length.toNat≤2^64 ∧ out.toNat+(length.toNat+6)≤2^64 ∧
      DisjointSpans key length.toNat out (length.toNat+6) := by
  unfold rawError at h
  cases he : typeError kind length cap with
  | some e => simp [he] at h
  | none =>
    simp only [he] at h
    split at h
    · rename_i hr
      obtain ⟨hk,hl,hcap⟩ := typeError_none kind length cap he
      have hranges : key.toNat+length.toNat≤2^64 ∧ out.toNat+(length+6).toNat≤2^64 ∧
          DisjointSpans key length.toNat out (length+6).toNat := hr
      have hlen := validated_lengths kind length cap he
      have hlen6 : (length+6).toNat=length.toNat+6 := by
        rcases hlen with h | h <;> rw [h.1] <;> decide
      have hc : length.toNat+6≤cap.toNat := by rw [←hlen6]; exact hcap
      refine ⟨kind_exact kind |>.mp hk,?_,hlen6,hc,hranges.1,?_,?_⟩
      · rcases hk with rfl | rfl <;> subst length <;> decide
      · simpa only [hlen6] using hranges.2.1
      · simpa only [hlen6] using hranges.2.2
    · cases h

end Libp2pAsm.Refinement.Identity.Peer
