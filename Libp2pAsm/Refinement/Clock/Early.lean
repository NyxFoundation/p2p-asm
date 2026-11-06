import Libp2pAsm.Refinement.Clock.Programs
import Libp2pAsm.Refinement.AsmCodec.Programs

open Libp2pAsm.Rv64 Libp2pAsm.Rv64.Logic in
macro "clock_read_step" : tactic => `(tactic| (
  apply WriteTrace.cons
  · simp [advance_eq_atPC]
  · simp only [advance_eq_atPC, pc_atPC, State.pc_setReg]
    conv => lhs; cbv
    try rfl
  · simp [execInstr, loadReg, bind, Except.bind, pure, Except.pure,
      writeReg, branch, jump_eq_atPC, advance_eq_atPC, getReg_setReg, *]
    <;> (try simp_all) <;> first | rfl | (split <;> first | omega | rfl)
  · trivial))

open Libp2pAsm.Rv64 Libp2pAsm.Rv64.Logic in
macro "clock_early_finish " n:term : tactic => `(tactic| (
  simp only [BitVec.ofNat_eq_ofNat] at *
  refine ⟨$n, ?_⟩
  apply Exists.intro
  refine ⟨by decide, ?trace, ?pc, ?out⟩
  case trace =>
    repeat clock_read_step
    exact .nil _
  all_goals simp_all [Libp2pAsm.Refinement.AsmCodec.Output, getReg_setReg]))

namespace Libp2pAsm.Refinement.Clock

open Rv64 Rv64.Logic AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

structure RawState where
  mode : Word
  afterNs : Word
  seconds : Word
  nanos : Word
  deriving Repr

def RawState.toSpec (s : RawState) : Spec.Clock.State :=
  ⟨s.mode.toNat, s.afterNs.toNat, s.seconds.toInt, s.nanos.toNat⟩

def StateAt (m : Memory) (ptr : Word) (s : RawState) : Prop :=
  ptr.toNat+32 ≤ 2^64 ∧ WordAt m ptr s.mode ∧ WordAt m (ptr+8) s.afterNs ∧
    WordAt m (ptr+16) s.seconds ∧ WordAt m (ptr+24) s.nanos

/-- Invalid limits return before any load or store, for all pointers and register contents. -/
theorem invalid_limits_trace (s : State) (hra : s.getReg .x1 = 0)
    (hbad : s.getReg .x12 = 0 ∨ s.getReg .x13 = 0 ∨ s.getReg .x12 < s.getReg .x13) :
    ∃ n t, n ≤ 256 ∧ WriteTrace program 0 0 0 n (atPC s 65536) t ∧
      t.pc = 0 ∧ Output 3 0 0 t := by
  by_cases hd : s.getReg .x12 = 0
  · clock_early_finish 5
  by_cases hs : s.getReg .x13 = 0
  · clock_early_finish 6
  have hlt : ¬s.getReg .x13 ≤ s.getReg .x12 := by
    have hh : s.getReg .x12 < s.getReg .x13 := hbad.resolve_left hd |>.resolve_left hs
    exact BitVec.not_le.mpr hh
  clock_early_finish 7

/-- Invalid modes and noncanonical previous nanos in modes 1/4 return before sample loads. -/
theorem invalid_state_trace (s : State) (old : RawState) (hra : s.getReg .x1 = 0)
    (hm : s.memory.valid = true) (hstate : StateAt s.memory (s.getReg .x10) old)
    (hd : s.getReg .x12 ≠ 0) (hs : s.getReg .x13 ≠ 0) (hspan : s.getReg .x13 ≤ s.getReg .x12)
    (hbad : ¬old.mode ≤ 4 ∨ ((old.mode = 1 ∨ old.mode = 4) ∧ ¬old.nanos < 1000000000)) :
    ∃ n t, n ≤ 256 ∧ WriteTrace program 0 0 0 n (atPC s 65536) t ∧
      t.pc = 0 ∧ Output 4 0 0 t := by
  have lmode := hstate.2.1.load hm
  by_cases hmode : old.mode ≤ 4
  case neg => clock_early_finish 11
  have lafter := hstate.2.2.1.load hm
  have lseconds := hstate.2.2.2.1.load hm
  have lnanos := hstate.2.2.2.2.load hm
  obtain ⟨hwhich, hns⟩ := hbad.resolve_left (not_not_intro hmode)
  rcases hwhich with hwhich | hwhich
  · clock_early_finish 20
  · clock_early_finish 18

/-- Stopped mode is sticky; previous nanos are unrestricted and the sample is never loaded. -/
theorem stopped_trace (s : State) (old : RawState) (hra : s.getReg .x1 = 0)
    (hm : s.memory.valid = true) (hstate : StateAt s.memory (s.getReg .x10) old)
    (hd : s.getReg .x12 ≠ 0) (hs : s.getReg .x13 ≠ 0) (hspan : s.getReg .x13 ≤ s.getReg .x12)
    (hmode : old.mode = 3) :
    ∃ n t, n ≤ 256 ∧ WriteTrace program 0 0 0 n (atPC s 65536) t ∧
      t.pc = 0 ∧ Output 2 0 0 t := by
  have lmode := hstate.2.1.load hm
  have lafter := hstate.2.2.1.load hm
  have lseconds := hstate.2.2.2.1.load hm
  have lnanos := hstate.2.2.2.2.load hm
  clock_early_finish 21

end Libp2pAsm.Refinement.Clock
