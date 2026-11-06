import Libp2pAsm.Refinement.AsmBuffer.Raw

open Libp2pAsm.Rv64 Libp2pAsm.Rv64.Logic in
macro "buffer_step" : tactic => `(tactic| (
  apply Trace.cons
  · simp [advance_eq_atPC]
  · apply step_of_fetch
    · simp only [advance_eq_atPC, pc_atPC, State.pc_setReg]
      conv => lhs; cbv
      try rfl
    · simp [execInstr, loadReg, bind, Except.bind, pure, Except.pure,
        writeReg, branch, jump_eq_atPC, advance_eq_atPC, getReg_setReg, *]
      <;> (try simp_all) <;> first | rfl | (split <;> first | omega | rfl)))

open Libp2pAsm.Rv64 Libp2pAsm.Rv64.Logic in
macro "buffer_finish " n:term : tactic => `(tactic| (
  simp only [BitVec.ofNat_eq_ofNat] at *
  refine ⟨$n, ?_⟩
  apply Exists.intro
  refine ⟨by decide, ?trace, ?pc, ?out⟩
  case trace =>
    repeat buffer_step
    exact .nil _
  all_goals simp_all [Libp2pAsm.Refinement.AsmBuffer.RawPost,
    Libp2pAsm.Refinement.AsmBuffer.rawResult,
    Libp2pAsm.Refinement.AsmCodec.Output, getReg_setReg]))

namespace Libp2pAsm.Refinement.AsmBuffer

open Rv64 Rv64.Logic

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Invalid access is rejected before any load, independent of reference/table addresses. -/
theorem invalid_access (s : State) (hra : s.getReg .x1 = 0)
    (ha : ¬s.getReg .x13 ≤ 1) :
    ∃ n t, n ≤ 96 ∧ Trace program 0 n (atPC s 65536) t ∧ t.pc = 0 ∧ RawPost (4, 0, 0) t := by
  simp only [BitVec.ofNat_eq_ofNat] at hra ha
  refine ⟨6, ?_⟩
  apply Exists.intro
  refine ⟨by decide, ?trace, ?pc, ?out⟩
  case trace =>
    repeat buffer_step
    exact .nil _
  all_goals simp_all [RawPost, AsmCodec.Output, getReg_setReg, advance_eq_atPC]

/-- Total raw-ABI execution with actual fetch and owned byte representations.
All branch decisions are universally quantified; no success condition is assumed. -/
theorem raw_trace (s : State) (ref : RawReference) (r : RawRegion)
    (hra : s.getReg .x1 = 0) (hm : s.memory.valid = true)
    (href : ReferenceAt s.memory (s.getReg .x11) ref)
    (hregion : RegionAt s.memory (s.getReg .x10) (s.getReg .x12) (s.getReg .x13) ref r) :
    ∃ n t, n ≤ 96 ∧ Trace program 0 n (atPC s 65536) t ∧ t.pc = 0 ∧
      RawPost (rawResult (s.getReg .x10) (s.getReg .x12) (s.getReg .x13) ref r) t := by
  by_cases ha : s.getReg .x13 ≤ 1
  case neg => buffer_finish 6
  by_cases hc : s.getReg .x12 >>> (59 : Nat) = 0
  case neg => buffer_finish 8
  have lslot := href.2.1.load hm
  by_cases hs : ref.slot < s.getReg .x12
  case neg => buffer_finish 10
  by_cases ht : s.getReg .x10 ≤ s.getReg .x10 + (ref.slot <<< (5 : Nat))
  case neg => buffer_finish 13
  obtain ⟨_, ownGen, ownBase, ownCap, ownFlags⟩ := hregion ha hc hs ht
  have lgen := ownGen.load hm
  have lbase := ownBase.load hm
  have lcap := ownCap.load hm
  have lflags := ownFlags.load hm
  by_cases hf : r.flags >>> (2 : Nat) = 0
  case neg => buffer_finish 16
  by_cases hactive : r.flags &&& 1 = 0
  · buffer_finish 18
  have lrgen := href.2.2.1.load hm
  by_cases hg : r.generation = ref.generation
  case neg => buffer_finish 21
  by_cases hcap : r.capacity = 0
  · buffer_finish 24
  by_cases hb : r.base ≤ r.base+r.capacity
  case neg => buffer_finish 26
  by_cases hw : s.getReg .x13 ≠ 0 ∧ r.flags &&& 2 = 0
  · obtain ⟨haccess, hreadonly⟩ := hw
    buffer_finish 29
  have lrlen := href.2.2.2.2.load hm
  have lroff := href.2.2.2.1.load hm
  by_cases hl : ref.length ≤ r.capacity
  case neg =>
    by_cases hz : s.getReg .x13 = 0
    · buffer_finish 30
    · have hwrite : r.flags &&& 2 ≠ 0 := fun h => hw ⟨hz, h⟩
      buffer_finish 33
  by_cases ho : ref.offset ≤ r.capacity-ref.length
  case neg =>
    by_cases hz : s.getReg .x13 = 0
    · buffer_finish 32
    · have hwrite : r.flags &&& 2 ≠ 0 := fun h => hw ⟨hz, h⟩
      buffer_finish 35
  by_cases hz : s.getReg .x13 = 0
  · buffer_finish 33
  · have hwrite : r.flags &&& 2 ≠ 0 := fun h => hw ⟨hz, h⟩
    buffer_finish 36

end Libp2pAsm.Refinement.AsmBuffer
