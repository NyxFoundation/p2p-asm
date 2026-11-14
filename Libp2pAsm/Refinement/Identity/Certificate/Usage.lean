import Libp2pAsm.Asm.Identity.Certificate.Usage
import Libp2pAsm.Rv64.Execution

namespace Libp2pAsm.Refinement.Identity.Certificate
open Rv64 Asm.Identity.Certificate

def usageAfter (s : State) : State :=
  (s.setReg .x5 (s.getReg .x5 &&& s.getReg .x6)).advance

theorem usage_instruction_execution (s : State) :
    execInstr usageInstruction s = .ok (usageAfter s) := rfl

theorem usage_sequence_execution (s : State) :
    execSequence [usageInstruction] s = .ok (usageAfter s) := rfl

theorem usage_memory_unchanged (s : State) : (usageAfter s).memory = s.memory := rfl
theorem usage_pc (s : State) : (usageAfter s).pc = s.pc + 4 := rfl

theorem usage_result (s : State) :
    (usageAfter s).getReg .x5 = s.getReg .x5 &&& s.getReg .x6 := by
  simp [usageAfter, LeanAsm.Rv64.State.advance, LeanAsm.Rv64.State.setReg, LeanAsm.Rv64.State.getReg, LeanAsm.Rv64.Reg.toNat]

theorem usage_preserves_callee (s : State) (r : Reg)
    (hr : r ≠ .x5) : (usageAfter s).getReg r = s.getReg r := by
  cases r <;> simp_all [usageAfter, LeanAsm.Rv64.State.advance, LeanAsm.Rv64.State.setReg, LeanAsm.Rv64.State.getReg, LeanAsm.Rv64.Reg.toNat]

end Libp2pAsm.Refinement.Identity.Certificate
