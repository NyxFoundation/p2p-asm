import Libp2pAsm.Refinement.Identity.PeerTypes

namespace Libp2pAsm.Refinement.Identity.Peer
open Rv64 Rv64.Logic Rv64.Logic.Parser

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

theorem key_range (s : State) (hn : s.getReg .x12≠0) (hra : s.getReg .x1=0) :
    ∃ n t, n≤21 ∧ AccessTrace program 0 [] [] n (atPC s 65776) t ∧
      (if (s.getReg .x11).toNat+(s.getReg .x12).toNat≤2^64 then
        t.pc=65868 ∧ Args s t ∧ t.getReg .x29=s.getReg .x29 else t.pc=0 ∧ ErrorOutput 4 t) := by
  by_cases hspan : (s.getReg .x11).toNat+(s.getReg .x12).toNat≤2^64
  · have hg := (range_iff (s.getReg .x11) (s.getReg .x12) hn).mpr hspan
    change s.getReg .x12+18446744073709551615≤(18446744073709551615 : Word)-s.getReg .x11 at hg
    refine ⟨6,?_,by decide,?trace,?post⟩
    case trace =>
      repeat parser_access_step
      exact .nil _
    case post => simp [hspan,Args,getReg_setReg]
  · have hg := mt (range_iff (s.getReg .x11) (s.getReg .x12) hn).mp hspan
    change ¬s.getReg .x12+18446744073709551615≤(18446744073709551615 : Word)-s.getReg .x11 at hg
    simp only [BitVec.ofNat_eq_ofNat] at *
    have hp : ∃ a, AccessTrace program 0 [] [] 5 (atPC s 65776) a ∧ a.pc=65796 ∧ a.getReg .x1=0 := by
      refine ⟨?_,?trace,?post⟩
      case trace =>
        repeat parser_access_step
        exact .nil _
      case post => simp [getReg_setReg,hra]
    obtain ⟨a,ha,hpc,hr⟩ := hp
    obtain ⟨t,ht,hret,ho,_⟩ := error_return 3 a hr
    exact ⟨21,t,by decide,by simpa using ha.append (accessTrace_at_pc hpc ht),
      by simpa only [if_neg hspan,BitVec.ofNat_eq_ofNat] using And.intro hret (show ErrorOutput 4 t from ho)⟩

end Libp2pAsm.Refinement.Identity.Peer
