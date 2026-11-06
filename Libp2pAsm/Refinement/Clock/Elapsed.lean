import Libp2pAsm.Refinement.Clock.Anchor
import Libp2pAsm.Refinement.Clock.ElapsedArithmetic

namespace Libp2pAsm.Refinement.Clock

open Rv64 Rv64.Logic AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

theorem backwards_wall_trace (s : State) (old : RawState) (sample : RawSample) (base ptr drift span : Word)
    (hra : s.getReg .x1 = 0) (hr : SampleReady s old sample base ptr drift span)
    (hbad : sample.seconds.toInt < old.seconds.toInt ∨
      (sample.seconds = old.seconds ∧ ¬old.nanos ≤ sample.nanos)) :
    ∃ n t, n ≤ 8 ∧ WriteTrace program 0 0 0 n (atPC s 66128) t ∧
      t.pc = 0 ∧ Output 1 0 0 t ∧ t.memory = s.memory := by
  obtain ⟨⟨hbase, hmode, hold, holdseconds, holdnanos, hbillion, hptr, hdrift, hspan⟩,
    hseconds, hnanos, hafter⟩ := hr
  by_cases hlt : sample.seconds.toInt < old.seconds.toInt
  · have hslt : sample.seconds.slt old.seconds = true := by simp [BitVec.slt_eq_decide, hlt]
    clock_mutation_finish 6
  · have hslt : sample.seconds.slt old.seconds = false := by simp [BitVec.slt_eq_decide, hlt]
    obtain ⟨heq, hns⟩ := hbad.resolve_left hlt
    clock_mutation_finish 8

def DifferenceReady (s : State) (base high low mono drift : Word) : Prop :=
  s.getReg .x5 = base ∧ s.getReg .x28 = high ∧ s.getReg .x29 = low ∧
    s.getReg .x11 = mono ∧ s.getReg .x12 = drift

def nanosWith (old : RawState) (sample : RawSample) (factor : Word) : Word :=
  if sample.nanos < old.nanos then sample.nanos+factor-old.nanos else sample.nanos-old.nanos

def lowWith (seconds nanos factor : Word) : Word := seconds*factor+nanos

def highWith (seconds nanos factor : Word) : Word :=
  BitVec.ofNat 64 (seconds.toNat*factor.toNat/2^64)+
    (if lowWith seconds nanos factor < seconds*factor then 1 else 0)

def ProductReady (s : State) (base seconds nanos factor after before drift : Word) : Prop :=
  s.getReg .x5 = base ∧ s.getReg .x30 = seconds ∧ s.getReg .x16 = nanos ∧
    s.getReg .x17 = factor ∧ s.getReg .x31 = after ∧ s.getReg .x7 = before ∧ s.getReg .x12 = drift

macro "clock_parts_finish " n:term : tactic => `(tactic| (
  simp only [BitVec.ofNat_eq_ofNat] at *
  refine ⟨$n, ?_⟩
  apply Exists.intro
  refine ⟨by decide, ?trace, ?pc, ?inv, ?memory, ?ra⟩
  case trace =>
    repeat clock_read_step
    exact .nil _
  all_goals simp_all [ProductReady, getReg_setReg]))

theorem parts_prefix (s : State) (old : RawState) (sample : RawSample) (base factor drift : Word)
    (hbase : s.getReg .x5 = base) (hold : s.getReg .x7 = old.afterNs)
    (holdseconds : s.getReg .x28 = old.seconds) (holdnanos : s.getReg .x29 = old.nanos)
    (hbillion : s.getReg .x17 = factor) (hdrift : s.getReg .x12 = drift)
    (hsecondsreg : s.getReg .x14 = sample.seconds) (hnanos : s.getReg .x15 = sample.nanos)
    (hafter : s.getReg .x31 = sample.afterNs)
    (hseconds : old.seconds.toInt ≤ sample.seconds.toInt)
    (hequal : sample.seconds = old.seconds → old.nanos ≤ sample.nanos) :
    ∃ n t, n ≤ 9 ∧ WriteTrace program 0 0 0 n (atPC s 66128) t ∧ t.pc = 66216 ∧
      ProductReady t base (secondsPart old sample) (nanosWith old sample factor) factor
        sample.afterNs old.afterNs drift ∧ t.memory = s.memory ∧ t.getReg .x1 = s.getReg .x1 := by
  have hslt : sample.seconds.slt old.seconds = false := by simp [BitVec.slt_eq_decide]; omega
  by_cases heq : sample.seconds = old.seconds
  · have hns := hequal heq
    have hnslt : ¬sample.nanos < old.nanos := BitVec.not_lt.mpr hns
    have hsp : secondsPart old sample = 0 := by simp [secondsPart, hnslt, heq]
    have hnp : nanosWith old sample factor = sample.nanos-old.nanos := by simp [nanosWith, hnslt]
    clock_parts_finish 8
  by_cases hns : sample.nanos < old.nanos
  · have hnsle : ¬old.nanos ≤ sample.nanos := BitVec.not_le.mpr hns
    have hsp : secondsPart old sample = sample.seconds-old.seconds+18446744073709551615 := by simp [secondsPart, hns]
    have hnp : nanosWith old sample factor = sample.nanos+factor-old.nanos := by simp [nanosWith, hns]
    clock_parts_finish 9
  · have hnsle : old.nanos ≤ sample.nanos := BitVec.not_lt.mp hns
    have hsp : secondsPart old sample = sample.seconds-old.seconds := by simp [secondsPart, hns]
    have hnp : nanosWith old sample factor = sample.nanos-old.nanos := by simp [nanosWith, hns]
    clock_parts_finish 6


theorem product_prefix (s : State) (base seconds nanos factor after before drift : Word)
    (hr : ProductReady s base seconds nanos factor after before drift) :
    ∃ t, WriteTrace program 0 0 0 6 (atPC s 66216) t ∧ t.pc = 66240 ∧
      DifferenceReady t base (highWith seconds nanos factor) (lowWith seconds nanos factor)
        (after-before) drift ∧ t.memory = s.memory ∧ t.getReg .x1 = s.getReg .x1 := by
  obtain ⟨hbase, hseconds, hnanos, hfactor, hafter, hbefore, hdrift⟩ := hr
  apply Exists.intro
  refine ⟨?trace, ?pc, ?inv, ?mem, ?ra⟩
  case trace =>
    repeat clock_read_step
    exact .nil _
  all_goals simp_all [DifferenceReady, highWith, lowWith, getReg_setReg]

theorem elapsed_words_prefix (s : State) (old : RawState) (sample : RawSample) (base factor drift : Word)
    (hbase : s.getReg .x5 = base) (hold : s.getReg .x7 = old.afterNs)
    (holdseconds : s.getReg .x28 = old.seconds) (holdnanos : s.getReg .x29 = old.nanos)
    (hbillion : s.getReg .x17 = factor) (hdrift : s.getReg .x12 = drift)
    (hsecondsreg : s.getReg .x14 = sample.seconds) (hnanos : s.getReg .x15 = sample.nanos)
    (hafter : s.getReg .x31 = sample.afterNs)
    (hseconds : old.seconds.toInt ≤ sample.seconds.toInt)
    (hequal : sample.seconds = old.seconds → old.nanos ≤ sample.nanos) :
    ∃ n t, n ≤ 15 ∧ WriteTrace program 0 0 0 n (atPC s 66128) t ∧ t.pc = 66240 ∧
      DifferenceReady t base (highWith (secondsPart old sample) (nanosWith old sample factor) factor)
        (lowWith (secondsPart old sample) (nanosWith old sample factor) factor)
        (sample.afterNs-old.afterNs) drift ∧ t.memory = s.memory ∧ t.getReg .x1 = s.getReg .x1 := by
  obtain ⟨n, a, hn, ht, hp, hr, hm, ha⟩ := parts_prefix s old sample base factor drift hbase hold
    holdseconds holdnanos hbillion hdrift hsecondsreg hnanos hafter hseconds hequal
  obtain ⟨t, htp, hpp, hrp, hmp, hap⟩ := product_prefix a base _ _ factor _ _ drift hr
  exact ⟨n+6, t, by omega, ht.append (writeTrace_at_pc hp htp), hpp, hrp, hmp.trans hm, hap.trans ha⟩


theorem elapsed_prefix (s : State) (old : RawState) (sample : RawSample) (base ptr drift span : Word)
    (hr : SampleReady s old sample base ptr drift span)
    (hseconds : old.seconds.toInt ≤ sample.seconds.toInt)
    (hequal : sample.seconds = old.seconds → old.nanos ≤ sample.nanos) :
    ∃ n t, n ≤ 15 ∧ WriteTrace program 0 0 0 n (atPC s 66128) t ∧ t.pc = 66240 ∧
      DifferenceReady t base (elapsedHigh (secondsPart old sample) (nanosPart old sample))
        (elapsedLow (secondsPart old sample) (nanosPart old sample))
        (sample.afterNs-old.afterNs) drift ∧ t.memory = s.memory ∧ t.getReg .x1 = s.getReg .x1 := by
  obtain ⟨⟨hbase, hmode, hold, holdseconds, holdnanos, hbillion, hptr, hdrift, hspan⟩,
    hsecondsreg, hnanos, hafter⟩ := hr
  exact elapsed_words_prefix s old sample base 1000000000 drift hbase hold holdseconds holdnanos
    hbillion hdrift hsecondsreg hnanos hafter hseconds hequal

end Libp2pAsm.Refinement.Clock
