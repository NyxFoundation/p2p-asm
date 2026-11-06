import Libp2pAsm.Refinement.Clock.Contract
import Libp2pAsm.Codegen.Input

namespace Libp2pAsm.Tests.AbiProof.ClockUpdate

open Rv64 Rv64.Logic Refinement.AsmCodec Refinement.Clock

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private instance : DecidableEq Spec.Clock.State := fun a b =>
  decidable_of_iff (a.mode = b.mode ∧ a.afterNs = b.afterNs ∧ a.seconds = b.seconds ∧ a.nanos = b.nanos)
    (by cases a; cases b; simp)

structure Fixture where
  old : RawState := ⟨1, 100, 0, 0⟩
  sample : RawSample := ⟨0, 100, 101, 0, 1⟩
  drift : Word := 1
  span : Word := 1

def stateBytes (f : Fixture) : Array UInt8 :=
  (Codegen.wordBytes [f.old.mode, f.old.afterNs, f.old.seconds, f.old.nanos]).data ++ Array.replicate 8 0xa5

def sampleBytes (f : Fixture) : Array UInt8 :=
  (Codegen.wordBytes [f.sample.status, f.sample.beforeNs, f.sample.afterNs, f.sample.seconds, f.sample.nanos]).data

def frame (f : Fixture) : List Region :=
  [⟨196608, sampleBytes f, false⟩, ⟨262144, Array.replicate 16 0xcc, true⟩]

def entry (f : Fixture) : State :=
  let s : State := { pc := 524288, memory := heap 131072 (stateBytes f) true (frame f) }
  (((s.setReg .x1 525104).setReg .x10 131072).setReg .x11 196608).setReg .x12 f.drift |>.setReg .x13 f.span

theorem stateBytes_size (f : Fixture) : (stateBytes f).size = 40 := by
  simp [stateBytes, Codegen.wordBytes, List.range_succ, List.foldl]

theorem sampleBytes_size (f : Fixture) : (sampleBytes f).size = 40 := by
  simp [sampleBytes, Codegen.wordBytes, List.range_succ, List.foldl]

theorem invocation (f : Fixture) :
    Invocation program (relocated program 524288) 524288 ((entry f).getReg .x1) 0 (entry f).memory := by
  refine ⟨⟨?_, by decide, by decide, by decide, ?_⟩,
    ⟨by decide, by decide, ?_, ?_⟩, CodeSlice.refl _⟩
  · change (heap 131072 (stateBytes f) true (frame f)).valid = true
    simp only [Memory.valid, Bool.and_eq_true]
    constructor
    · rw [Array.all_eq_true]
      intro i hi
      have he : i = 0 ∨ i = 1 ∨ i = 2 := by change i < 3 at hi; omega
      rcases he with rfl | rfl | rfl <;> simp [heap, frame, Region.valid, Region.endAddr, stateBytes_size, sampleBytes_size]
    · simp [heap, frame, Region.disjoint, Region.endAddr, stateBytes_size, sampleBytes_size]
  · intro r hr hw
    simp [entry, heap, frame] at hr
    rcases hr with rfl | rfl | rfl <;> left <;> simp [Region.endAddr, stateBytes_size, sampleBytes_size, relocated]
  · simp [entry, getReg_setReg]
  · right
    change 524288+4*program.code.size ≤ 525104
    decide

def Verified (f : Fixture) : Prop :=
  ∃ (done : Completed) (after : RawState) (outBytes : Array UInt8),
    Returns (relocated program 524288) (relocated program 524288) 525104 256 (entry f) done ∧
    Output (BitVec.ofNat 64 (Spec.Clock.update f.old.toSpec f.sample.toSpec f.drift.toNat f.span.toNat).1.code) 0 0 done.state ∧
    after.toSpec = (Spec.Clock.update f.old.toSpec f.sample.toSpec f.drift.toNat f.span.toNat).2 ∧
    StateAt done.state.memory 131072 after ∧ done.state.memory = heap 131072 outBytes true (frame f) ∧
    ByteFrame 0 32 (stateBytes f) outBytes ∧ WriteTrace (relocated program 524288) 525104 131072 131104
      done.steps (entry f) done.state

theorem verify (f : Fixture) (ho : StateBytes (stateBytes f) f.old)
    (hs : SampleAt (entry f).memory 196608 f.sample) : Verified f := by
  exact check_embedded _ _ 0 (entry f) f.old f.sample (stateBytes f) (frame f) (invocation f) rfl
    rfl (by simp [entry, getReg_setReg]) (by rw [stateBytes_size]; decide) ho hs (by simp [entry, getReg_setReg])

macro "clock_sample_owned" : tactic => `(tactic| (
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_⟩
  all_goals refine ⟨1, ⟨by decide, by decide, by decide, by decide, by decide⟩⟩))

def initial : Fixture := { old := ⟨0, 18446744073709551615, 9223372036854775807, 18446744073709551615⟩, sample := ⟨0, 100, 101, 9223372036854775808, 0⟩ }

theorem initial_verified : Verified initial := verify initial (by unfold StateBytes; decide) (by clock_sample_owned)
theorem initial_expected : Spec.Clock.update initial.old.toSpec initial.sample.toSpec 1 1 =
    (.trusted, ⟨1, 101, -9223372036854775808, 0⟩) := by decide

def candidate : Fixture := { old := ⟨2, 100, 9223372036854775807, 18446744073709551615⟩ }
theorem candidate_verified : Verified candidate := verify candidate (by unfold StateBytes; decide) (by clock_sample_owned)
theorem candidate_expected : Spec.Clock.update candidate.old.toSpec candidate.sample.toSpec 1 1 =
    (.wallUnavailable, ⟨4, 101, 0, 1⟩) := by decide

def recovery : Fixture := { old := ⟨4, 101, 0, 1⟩, sample := ⟨0, 101, 102, 0, 2⟩ }
theorem recovery_verified : Verified recovery := verify recovery (by unfold StateBytes; decide) (by clock_sample_owned)
theorem recovery_expected : Spec.Clock.update recovery.old.toSpec recovery.sample.toSpec 1 1 =
    (.trusted, ⟨1, 102, 0, 2⟩) := by decide

def borrowNanos : Fixture := { old := ⟨1, 100, 0, 999999999⟩, sample := ⟨0, 100, 101, 1, 0⟩ }
theorem borrowNanos_verified : Verified borrowNanos := verify borrowNanos (by unfold StateBytes; decide) (by clock_sample_owned)
theorem borrowNanos_expected : Spec.Clock.update borrowNanos.old.toSpec borrowNanos.sample.toSpec 1 1 =
    (.trusted, ⟨1, 101, 1, 0⟩) := by decide

def backwards : Fixture := { old := ⟨1, 100, 9223372036854775807, 0⟩, sample := ⟨0, 100, 101, 9223372036854775808, 0⟩ }
theorem backwards_verified : Verified backwards := verify backwards (by unfold StateBytes; decide) (by clock_sample_owned)
theorem backwards_expected : Spec.Clock.update backwards.old.toSpec backwards.sample.toSpec 1 1 =
    (.wallUnavailable, ⟨4, 101, -9223372036854775808, 0⟩) := by decide

def hugeElapsed : Fixture := { old := ⟨1, 100, 9223372036854775808, 0⟩, sample := ⟨0, 100, 101, 9223372036854775807, 0⟩, drift := 18446744073709551615 }
theorem hugeElapsed_verified : Verified hugeElapsed := verify hugeElapsed (by unfold StateBytes; decide) (by clock_sample_owned)
theorem hugeElapsed_expected : Spec.Clock.update hugeElapsed.old.toSpec hugeElapsed.sample.toSpec 18446744073709551615 1 =
    (.wallUnavailable, ⟨4, 101, 9223372036854775807, 0⟩) := by decide

def borrowHigh : Fixture := { sample := ⟨0, 100, 101, 18446744073, 709551616⟩, drift := 18446744073709551615 }
theorem borrowHigh_verified : Verified borrowHigh := verify borrowHigh (by unfold StateBytes; decide) (by clock_sample_owned)
theorem borrowHigh_expected : Spec.Clock.update borrowHigh.old.toSpec borrowHigh.sample.toSpec 18446744073709551615 1 =
    (.trusted, ⟨1, 101, 18446744073, 709551616⟩) := by decide

def unavailable : Fixture := { sample := ⟨1, 100, 101, 9223372036854775808, 18446744073709551615⟩ }
theorem unavailable_verified : Verified unavailable := verify unavailable (by unfold StateBytes; decide) (by clock_sample_owned)
theorem unavailable_expected : Spec.Clock.update unavailable.old.toSpec unavailable.sample.toSpec 1 1 =
    (.wallUnavailable, ⟨2, 101, 0, 0⟩) := by decide

def monotonicFailure : Fixture := { sample := ⟨0, 18446744073709551615, 0, 0, 0⟩ }
theorem monotonicFailure_verified : Verified monotonicFailure := verify monotonicFailure (by unfold StateBytes; decide) (by clock_sample_owned)
theorem monotonicFailure_expected : Spec.Clock.update monotonicFailure.old.toSpec monotonicFailure.sample.toSpec 1 1 =
    (.monotonicFailure, ⟨3, 100, 0, 0⟩) := by decide

def invalidLimits : Fixture := { drift := 0, span := 0 }
theorem invalidLimits_verified : Verified invalidLimits := verify invalidLimits (by unfold StateBytes; decide) (by clock_sample_owned)
theorem invalidLimits_expected : Spec.Clock.update invalidLimits.old.toSpec invalidLimits.sample.toSpec 0 0 =
    (.invalidLimits, invalidLimits.old.toSpec) := by decide

def invalidState : Fixture := { old := ⟨4, 100, 0, 1000000000⟩ }
theorem invalidState_verified : Verified invalidState := verify invalidState (by unfold StateBytes; decide) (by clock_sample_owned)
theorem invalidState_expected : Spec.Clock.update invalidState.old.toSpec invalidState.sample.toSpec 1 1 =
    (.invalidState, invalidState.old.toSpec) := by decide

def stopped : Fixture := { old := ⟨3, 18446744073709551615, 9223372036854775808, 18446744073709551615⟩, sample := ⟨18446744073709551615, 0, 0, 0, 0⟩ }
theorem stopped_verified : Verified stopped := verify stopped (by unfold StateBytes; decide) (by clock_sample_owned)
theorem stopped_expected : Spec.Clock.update stopped.old.toSpec stopped.sample.toSpec 1 1 =
    (.monotonicFailure, stopped.old.toSpec) := by decide

end Libp2pAsm.Tests.AbiProof.ClockUpdate
