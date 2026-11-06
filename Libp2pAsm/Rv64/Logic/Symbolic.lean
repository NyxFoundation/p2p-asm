import Libp2pAsm.Rv64.Logic.Trace
import Libp2pAsm.Rv64.Logic.State

namespace Libp2pAsm.Rv64.Logic

theorem jump_eq_atPC (s : State) (d : Reg) (v : Word) :
    jump s d v = if v.toNat % 4 == 0 then .ok (atPC (s.setReg d (s.pc + 4)) v)
      else .error .instructionMisaligned := rfl

theorem storeReg_eq_atPC (s : State) (width : Nat) (a b : Reg) (off : BitVec 12) :
    storeReg s width a b off = (do
      let m ← s.memory.store width (s.getReg a + off.signExtend 64) (s.getReg b)
      pure (atPC (withMemory s m) (s.pc + 4))) := rfl

end Libp2pAsm.Rv64.Logic

open Libp2pAsm.Rv64 Libp2pAsm.Rv64.Logic in
/-- One symbolic instruction. Fetch and execution are separate kernel proof obligations. -/
macro "trace_step " i:term : tactic => `(tactic| (
  apply Trace.cons
  · simp [advance_eq_atPC]
  · apply step_of_fetch (i := $i)
    · simp only [advance_eq_atPC, pc_atPC, State.pc_setReg]
      rfl
    · simp [execInstr, loadReg, storeReg_eq_atPC, bind, Except.bind, pure, Except.pure,
        writeReg, branch, jump_eq_atPC, advance_eq_atPC, getReg_setReg, *]
      <;> (try simp_all) <;> first | rfl | (split <;> first | omega | rfl)))

open Libp2pAsm.Rv64 Libp2pAsm.Rv64.Logic in
/-- Keep input register values opaque while composing straight-line arithmetic. -/
macro "trace_step_plain " i:term : tactic => `(tactic| (
  apply Trace.cons
  · simp [advance_eq_atPC]
  · apply step_of_fetch (i := $i)
    · simp only [advance_eq_atPC, pc_atPC, State.pc_setReg]
      rfl
    · simp [execInstr, writeReg, branch, jump_eq_atPC, advance_eq_atPC, getReg_setReg]
      <;> rfl))

