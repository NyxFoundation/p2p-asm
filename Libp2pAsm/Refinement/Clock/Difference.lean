import Libp2pAsm.Refinement.Clock.Elapsed
import Libp2pAsm.Refinement.Clock.DriftArithmetic

namespace Libp2pAsm.Refinement.Clock

open Rv64 Rv64.Logic AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

theorem difference_trace (s : State) (base high low mono drift : Word)
    (bytes : Array UInt8) (frame : List Region) (hra : s.getReg .x1 = 0)
    (hr : DifferenceReady s base high low mono drift) (hm : s.memory = heap base bytes true frame)
    (hv : (heap base bytes true frame).valid = true) (ha : base.toNat%8 = 0) (hb : 32 ≤ bytes.size) :
    ∃ n t, n ≤ 12 ∧ WriteTrace program 0 base.toNat (base.toNat+32) n (atPC s 66240) t ∧
      t.pc = 0 ∧ Output (if withinDrift high low mono drift then 0 else 1) 0 0 t ∧
        t.memory = heap base (if withinDrift high low mono drift then writeLE64 bytes 0 1 else bytes) true frame := by
  obtain ⟨hbase, hhigh, hlow, hmono, hdrift⟩ := hr
  clock_store_facts base bytes frame hv ha hb
  unfold withinDrift distanceHigh distanceLow
  by_cases hz : high = 0
  · simp only [if_pos hz, true_and]
    by_cases hlt : low < mono
    · have hge : ¬mono ≤ low := BitVec.not_le.mpr hlt
      simp only [if_pos hlt]
      by_cases hd : mono-low ≤ drift
      · simp only [if_pos hd]; clock_mutation_finish 12
      · simp only [if_neg hd]; clock_mutation_finish 10
    · have hge : mono ≤ low := BitVec.not_lt.mp hlt
      simp only [if_neg hlt]
      by_cases hd : low-mono ≤ drift
      · simp only [if_pos hd]; clock_mutation_finish 11
      · simp only [if_neg hd]; clock_mutation_finish 9
  simp only [if_neg hz]
  by_cases hlt : low < mono
  · simp only [if_pos hlt]
    by_cases hhi : high-1 = 0
    · simp only [hhi, true_and]
      by_cases hd : low-mono ≤ drift
      · simp only [if_pos hd]; clock_mutation_finish 12
      · simp only [if_neg hd]; clock_mutation_finish 10
    · simp only [hhi, false_and, ite_false]; clock_mutation_finish 9
  · have hge : mono ≤ low := BitVec.not_lt.mp hlt
    simp only [if_neg hlt, BitVec.ofNat_eq_ofNat] at hz ⊢
    simp only [BitVec.sub_zero, hz, false_and, ite_false]
    clock_mutation_finish 9

end Libp2pAsm.Refinement.Clock
