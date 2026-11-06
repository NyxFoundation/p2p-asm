import Libp2pAsm.Refinement.Clock.Early

namespace Libp2pAsm.Refinement.Clock

open Rv64 Rv64.Logic

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def Ready (s : State) (old : RawState) (ptr sample drift span : Word) : Prop :=
  s.getReg .x5 = ptr ∧ s.getReg .x6 = old.mode ∧ s.getReg .x7 = old.afterNs ∧
  s.getReg .x28 = old.seconds ∧ s.getReg .x29 = old.nanos ∧ s.getReg .x17 = 1000000000 ∧
  s.getReg .x11 = sample ∧ s.getReg .x12 = drift ∧ s.getReg .x13 = span

macro "clock_prefix_finish " n:term : tactic => `(tactic| (
  simp only [BitVec.ofNat_eq_ofNat] at *
  refine ⟨$n, ?_⟩
  apply Exists.intro
  refine ⟨by decide, ?trace, ?pc, ?inv, ?memory, ?ra⟩
  case trace =>
    repeat clock_read_step
    exact .nil _
  all_goals simp_all [Ready, getReg_setReg]))

theorem valid_state_prefix (s : State) (old : RawState)
    (hm : s.memory.valid = true) (hstate : StateAt s.memory (s.getReg .x10) old)
    (hd : s.getReg .x12 ≠ 0) (hs : s.getReg .x13 ≠ 0) (hspan : s.getReg .x13 ≤ s.getReg .x12)
    (hmode : old.mode ≤ 4) (hnanos : (old.mode = 1 ∨ old.mode = 4) → old.nanos < 1000000000)
    (hstop : old.mode ≠ 3) :
    ∃ n t, n ≤ 19 ∧ WriteTrace program 0 0 0 n (atPC s 65536) t ∧ t.pc = 65760 ∧
      Ready t old (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13) ∧
      t.memory = s.memory ∧ t.getReg .x1 = s.getReg .x1 := by
  have lmode := hstate.2.1.load hm
  have lafter := hstate.2.2.1.load hm
  have lseconds := hstate.2.2.2.1.load hm
  have lnanos := hstate.2.2.2.2.load hm
  by_cases hm4 : old.mode = 4
  · have hns := hnanos (Or.inr hm4)
    clock_prefix_finish 19
  by_cases hm1 : old.mode = 1
  · have hns := hnanos (Or.inl hm1)
    clock_prefix_finish 19
  clock_prefix_finish 17

end Libp2pAsm.Refinement.Clock
