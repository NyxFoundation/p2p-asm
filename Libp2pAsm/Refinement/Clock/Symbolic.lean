import Libp2pAsm.Refinement.Clock.Memory

open Libp2pAsm.Rv64 Libp2pAsm.Rv64.Logic Libp2pAsm.Refinement.Clock in
macro "clock_store_facts " base:ident bytes:ident frame:ident hv:ident ha:ident hb:ident : tactic => `(tactic| (
  have hs0 (after : Array UInt8) (value : Word) (hlen : after.size = ($bytes).size) :
      (heap $base after true $frame).store 8 $base value =
        .ok (heap $base (writeLE64 after 0 value) true $frame) := by
    simpa using store_at $base value $bytes after $frame $hv $ha hlen 0 (by decide) (by omega)
  have hs8 (after : Array UInt8) (value : Word) (hlen : after.size = ($bytes).size) :
      (heap $base after true $frame).store 8 ($base+8) value =
        .ok (heap $base (writeLE64 after 8 value) true $frame) := by
    exact store_at $base value $bytes after $frame $hv $ha hlen 8 (by decide) (by omega)
  have hs16 (after : Array UInt8) (value : Word) (hlen : after.size = ($bytes).size) :
      (heap $base after true $frame).store 8 ($base+16) value =
        .ok (heap $base (writeLE64 after 16 value) true $frame) := by
    exact store_at $base value $bytes after $frame $hv $ha hlen 16 (by decide) (by omega)
  have hs24 (after : Array UInt8) (value : Word) (hlen : after.size = ($bytes).size) :
      (heap $base after true $frame).store 8 ($base+24) value =
        .ok (heap $base (writeLE64 after 24 value) true $frame) := by
    exact store_at $base value $bytes after $frame $hv $ha hlen 24 (by decide) (by omega)
  have hb0 : ($base).toNat ≤ ($base).toNat ∧ ($base).toNat+8 ≤ ($base).toNat+32 := by omega
  have hb8 := store_bounds $base $bytes $frame $hv $hb 8 (by decide)
  have hb16 := store_bounds $base $bytes $frame $hv $hb 16 (by decide)
  have hb24 := store_bounds $base $bytes $frame $hv $hb 24 (by decide)
  simp only [BitVec.ofNat_eq_ofNat] at *))

open Libp2pAsm.Rv64 Libp2pAsm.Rv64.Logic in
macro "clock_write_step" : tactic => `(tactic| (
  apply WriteTrace.cons
  · simp [advance_eq_atPC]
  · simp only [advance_eq_atPC, pc_atPC, State.pc_setReg]
    conv => lhs; cbv
    try rfl
  · simp [execInstr, loadReg, storeReg_eq_atPC, bind, Except.bind, pure, Except.pure,
      writeReg, branch, jump_eq_atPC, advance_eq_atPC, getReg_setReg, *]
    <;> (try simp_all) <;> first | rfl | (split <;> first | omega | rfl)
  · first | trivial | (simp [WritesWithin, getReg_setReg, *] <;> simp_all)))

open Libp2pAsm.Rv64 Libp2pAsm.Rv64.Logic Libp2pAsm.Refinement.Clock in
macro "clock_mutation_finish " n:term : tactic => `(tactic| (
  try simp only [BitVec.ofNat_eq_ofNat] at *
  refine ⟨$n, ?_⟩
  apply Exists.intro
  refine ⟨by decide, ?trace, ?pc, ?out, ?memory⟩
  case trace =>
    repeat clock_write_step
    exact .nil _
  all_goals simp_all [Libp2pAsm.Refinement.AsmCodec.Output,
    stopBytes, sampleBytes, unavailableBytes, getReg_setReg]))
