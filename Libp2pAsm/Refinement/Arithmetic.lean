import Libp2pAsm.Asm.Arithmetic
import Libp2pAsm.Rv64.Execution
import Libp2pAsm.Refinement.Registers

namespace Libp2pAsm.Refinement

open Rv64

def returnTarget (s : State) : Word := s.getReg .x1 &&& (~~~(1 : Word))

def addPost (s : State) : State :=
  { s.setReg .x10 (s.getReg .x10 + s.getReg .x11) with pc := returnTarget s }

/-- The exact flattened instructions, including the ABI return, implement modular addition. -/
theorem addWords_sequence_correct (s : State)
    (h_aligned : (returnTarget s).toNat % 4 = 0) :
    execSequence Asm.addWords.flatten s = .ok (addPost s) := by
  simp [Asm.addWords, SAsm.Stmt.flatten, execSequence, execInstr, writeReg]
  let updated := s.setReg .x10 (s.getReg .x10 + s.getReg .x11)
  have h_ra : updated.advance.getReg .x1 = s.getReg .x1 := by
    exact State.getReg_setReg_other s .x10 .x1 _ (by decide)
  change jump updated.advance .x0
    (updated.advance.getReg .x1 &&& (~~~(1 : Word))) = .ok (addPost s)
  rw [h_ra]
  change jump updated.advance .x0 (returnTarget s) = .ok (addPost s)
  simp only [jump, h_aligned, beq_self_eq_true, if_true, State.setReg_zero]
  rfl

def addProgram : Program :=
  { base := 0x10000, code := Asm.addWords.flatten.toArray }

/-- The fetched program, not only an instruction list, returns in exactly two steps. -/
theorem addWords_run_correct (s : State) (hpc : s.pc = 0x10000)
    (hra : s.getReg .x1 = 0) (hvalid : addProgram.valid s.memory = true) :
    runUntil addProgram 0 2 s = .ok ⟨addPost s, 2⟩ := by
  let after := (s.setReg .x10 (s.getReg .x10 + s.getReg .x11)).advance
  have fetch0 : addProgram.fetch 0x10000 = .ok (.ADD .x10 .x10 .x11) := rfl
  have fetch1 : addProgram.fetch 0x10004 = .ok (.JALR .x0 .x1 0) := rfl
  have first : step addProgram s = .ok after := by
    unfold step
    rw [hpc, fetch0]
    rfl
  have pc1 : after.pc = 0x10004 := by
    simp [after, State.advance, hpc]
  have ra1 : after.getReg .x1 = 0 := by
    simpa [after] using (State.getReg_setReg_other s .x10 .x1
      (s.getReg .x10 + s.getReg .x11) (by decide)).trans hra
  have second : step addProgram after = .ok (addPost s) := by
    unfold step
    rw [pc1, fetch1]
    change jump after .x0 ((after.getReg .x1 + 0) &&& (~~~(1 : Word))) = .ok (addPost s)
    rw [ra1]
    simp [jump, addPost, returnTarget, hra, after, State.advance]
  unfold runUntil
  rw [hvalid]
  change runLoop addProgram 0 2 s 0 = .ok ⟨addPost s, 2⟩
  rw [runLoop, hpc]
  change (do runLoop addProgram 0 1 (← step addProgram s) 1) = .ok ⟨addPost s, 2⟩
  rw [first]
  change runLoop addProgram 0 1 after 1 = .ok ⟨addPost s, 2⟩
  rw [runLoop, pc1]
  change (do runLoop addProgram 0 0 (← step addProgram after) 2) = .ok ⟨addPost s, 2⟩
  rw [second]
  change runLoop addProgram 0 0 (addPost s) 2 = .ok ⟨addPost s, 2⟩
  simp [runLoop, addPost, returnTarget, hra]

end Libp2pAsm.Refinement
