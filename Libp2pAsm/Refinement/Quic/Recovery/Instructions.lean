import Libp2pAsm.Asm.Quic.Recovery.Send
import Libp2pAsm.Rv64.Execution
import Libp2pAsm.Refinement.Registers
import Libp2pAsm.Refinement.Quic.Recovery.Invariants

namespace Libp2pAsm.Refinement.Quic.Recovery
open Rv64

def carryPost (s : Rv64.State) : Rv64.State :=
  let sum := s.getReg .x5 + s.getReg .x6
  let t := (s.setReg .x28 sum).advance
  (t.setReg .x29 (if sum < s.getReg .x5 then 1 else 0)).advance

/-- Exact execution of the ADD/SLTU fragment used for amplification carries.
No synthetic opcode or pure Spec evaluator participates in execution. -/
theorem execute_carry (s : Rv64.State) :
    execSequence Asm.Quic.Recovery.carryInstructions s = .ok (carryPost s) := by
  simp [Asm.Quic.Recovery.carryInstructions, execSequence, execInstr, writeReg, carryPost,
    bind, Except.bind, State.advance, State.getReg, State.setReg, Reg.toNat]
  rfl

theorem carry_is_overflow (a b : Word) :
    a+b < a ↔ 2^64 ≤ a.toNat+b.toNat := by
  change (a+b).toNat < a.toNat ↔ _
  rw [BitVec.toNat_add]
  have ha := a.isLt
  have hb := b.isLt
  omega

theorem carry_reconstructs_sum (a b : Word) :
    (if a+b < a then 1 else 0)*2^64 + (a+b).toNat = a.toNat+b.toNat := by
  simp only [carry_is_overflow, BitVec.toNat_add]
  have ha := a.isLt
  have hb := b.isLt
  split <;> omega

theorem carry_preserves_memory (s : Rv64.State) :
    (carryPost s).memory = s.memory := by
  rfl

/-- Infix membership connects the proved fragment to an actual emitted leaf.
It is deliberately not presented as refinement of the full recovery transition. -/
theorem carry_occurs_in_amplification :
    Asm.Quic.Recovery.carryInstructions <:+:
      (Asm.Quic.Recovery.ampTest (Asm.Quic.Recovery.e 5) (Asm.Quic.Recovery.done 7)).flatten := by
  decide

end Libp2pAsm.Refinement.Quic.Recovery
