import Libp2pAsm.Refinement.Clock.EarlyContract
import Libp2pAsm.Codegen.Input

namespace Libp2pAsm.Tests.AbiProof.Clock

open Rv64 Rv64.Logic Refinement.AsmCodec Refinement.Clock

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def bytes (old : RawState) : Array UInt8 :=
  (Codegen.wordBytes [old.mode, old.afterNs, old.seconds, old.nanos]).data

def entry (old : RawState) (drift span : Word) : State :=
  let s : State := { pc := 524288, memory := heap 131072 (bytes old) true [] }
  (((s.setReg .x1 525104).setReg .x10 131072).setReg .x11 18446744073709551615).setReg .x12 drift
    |>.setReg .x13 span

theorem bytes_size (old : RawState) : (bytes old).size = 32 := by
  simp [bytes, Codegen.wordBytes, List.range_succ, List.foldl]

theorem invocation (old : RawState) (drift span : Word) :
    Invocation program (relocated program 524288) 524288 ((entry old drift span).getReg .x1) 0
      (entry old drift span).memory := by
  refine ⟨⟨?_, by decide, by decide, by decide, ?_⟩,
    ⟨by decide, by decide, ?_, ?_⟩, CodeSlice.refl _⟩
  · change (heap 131072 (bytes old) true []).valid = true
    simp [LeanAsm.Rv64.Memory.valid, heap, LeanAsm.Rv64.Region.valid, LeanAsm.Rv64.Region.endAddr, bytes_size]
  · intro r hr hw
    simp [entry, heap] at hr
    subst r
    left
    simp [LeanAsm.Rv64.Region.endAddr, bytes_size, relocated]
  · simp [entry, getReg_setReg]
  · right
    change 524288+4*program.code.size ≤ 525104
    decide

def invalid : RawState := ⟨1, 0, 0, 1000000000⟩
def stopped : RawState := ⟨3, 18446744073709551615, 9223372036854775808, 18446744073709551615⟩
def sample : Spec.Clock.Sample := ⟨18446744073709551615, 0, 0, 0, 0⟩

macro "clock_own_word" : tactic => `(tactic| (
  refine ⟨0, ⟨by decide, by decide, by decide, by decide, by decide⟩⟩))

theorem invalid_owned : StateAt (entry invalid 10 1).memory ((entry invalid 10 1).getReg .x10) invalid := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> clock_own_word

theorem stopped_owned : StateAt (entry stopped 10 1).memory ((entry stopped 10 1).getReg .x10) stopped := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> clock_own_word

theorem invalid_limits_no_sample : ReadOnlyReturn (relocated program 524288) 524288
    (entry invalid 0 1) .invalidLimits := by
  exact (invalid_limits_embedded _ _ 0 _ invalid.toSpec sample (invocation invalid 0 1)
    rfl (by decide)).1

theorem invalid_state_no_sample : ReadOnlyReturn (relocated program 524288) 524288
    (entry invalid 10 1) .invalidState := by
  exact (invalid_state_embedded _ _ 0 _ invalid sample (invocation invalid 10 1) rfl
    invalid_owned (by decide) (by decide) (by decide) (by decide)).1

theorem stopped_ignores_nanos_and_sample : ReadOnlyReturn (relocated program 524288) 524288
    (entry stopped 10 1) .monotonicFailure := by
  exact (stopped_embedded _ _ 0 _ stopped sample (invocation stopped 10 1) rfl
    stopped_owned (by decide) (by decide) (by decide) (by decide)).1

end Libp2pAsm.Tests.AbiProof.Clock
