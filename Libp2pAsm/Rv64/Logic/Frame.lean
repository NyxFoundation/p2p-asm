import Libp2pAsm.Rv64.Logic.Fetch
import Libp2pAsm.Rv64.Logic.State

namespace Libp2pAsm.Rv64.Logic

/-- The unique register destination, with x0 used for instructions without a write. -/
def destination : Instr → Reg
  | .ADD d .. | .SUB d .. | .AND d .. | .OR d .. | .XOR d ..
  | .SLL d .. | .SRL d .. | .SRA d .. | .SLT d .. | .SLTU d ..
  | .ADDI d .. | .ANDI d .. | .ORI d .. | .XORI d ..
  | .SLLI d .. | .SRLI d .. | .SRAI d .. | .LUI d .. | .AUIPC d ..
  | .MUL d .. | .MULHU d .. | .DIVU d .. | .REMU d ..
  | .ADDW d .. | .SUBW d .. | .SLTI d .. | .SLTIU d ..
  | .ADDIW d .. | .SLLIW d .. | .SRLIW d ..
  | .MULH d .. | .MULHSU d ..
  | .DIV d .. | .REM d ..
  | .LB d .. | .LH d .. | .LW d .. | .LHU d .. | .LWU d ..
  | .LBU d .. | .LD d .. | .JAL d .. | .JALR d .. => d
  | _ => .x0

def writesMemory : Instr → Bool
  | .SB .. | .SD .. | .SH .. | .SW .. => true
  | _ => false

private theorem writeReg_frame {s t : State} {d r : Reg} {v : Word}
    (hd : r ≠ destination (.ADDI d .x0 0)) (he : writeReg s d v = .ok t) :
    t.getReg r = s.getReg r := by
  simp only [writeReg, Except.ok.injEq] at he
  subst t
  simp only [State.getReg_advance, getReg_setReg]
  by_cases hr : r = .x0 <;> simp_all [destination]

/-- Invert a monadic bind whose result is `.ok`. -/
-- Invert a monadic bind whose result is `.ok`.
private theorem bind_eq_ok {ε α β} {result : Except ε α} {next : α → Except ε β} {b : β} :
    Bind.bind result next = .ok b ↔ ∃ value, result = .ok value ∧ next value = .ok b := by
  constructor
  · intro h
    cases result with
    | error e => cases h
    | ok v => exact ⟨v, rfl, h⟩
  · intro ⟨value, hv, hnext⟩
    cases hv
    exact hnext

private theorem jump_frame {s t : State} {d r : Reg} {v : Word}
    (hd : r ≠ d) (he : jump s d v = .ok t) : t.getReg r = s.getReg r := by
  unfold jump at he
  split at he
  · cases he
    change (s.setReg d (s.pc + 4)).getReg r = _
    by_cases hr : r = .x0 <;> simp [getReg_setReg, hr, hd]
  · cases he

theorem execInstr_register_frame {i : Instr} {s t : State} {r : Reg}
    (hd : r ≠ destination i) (he : execInstr i s = .ok t) :
    t.getReg r = s.getReg r := by
  cases i <;> simp only [execInstr] at he
  all_goals first
    | exact writeReg_frame hd he
    | exact jump_frame hd he
    | (simp only [execInstr, loadReg] at he
       rw [bind_eq_ok] at he
       obtain ⟨value, _, he⟩ := he
       exact writeReg_frame hd he)
    | (simp only [execInstr, storeReg] at he
       rw [bind_eq_ok] at he
       obtain ⟨memory, _, he⟩ := he
       simp only [pure, Except.pure] at he
       cases he
       rfl)
    | (simp only [execInstr, branch] at he
       split at he
       · exact jump_frame hd he
       · cases he; rfl)
    | (cases he; exact State.getReg_advance s r)

theorem execInstr_memory_frame {i : Instr} {s t : State}
    (hw : writesMemory i = false) (he : execInstr i s = .ok t) : t.memory = s.memory := by
  cases i <;> simp only [writesMemory] at hw <;> try cases hw
  all_goals simp only [execInstr, writeReg, loadReg, jump, branch,
    bind, Except.bind, LeanAsm.Rv64.State.advance] at he
  all_goals repeat split at he
  all_goals cases he
  all_goals simp [LeanAsm.Rv64.State.advance]

theorem Trace.register_frame {p stop n s t r} (h : Trace p stop n s t)
    (hd : ∀ i ∈ p.code, r ≠ destination i) : t.getReg r = s.getReg r := by
  apply h.invariant (P := fun u => u.getReg r = s.getReg r) rfl
  intro a b ha hs
  unfold step at hs
  cases hf : p.fetch a.pc with
  | error e => simp [hf, bind, Except.bind] at hs
  | ok i =>
    have he : execInstr i a = .ok b := by simpa [hf, bind, Except.bind] using hs
    exact (execInstr_register_frame (hd i (fetch_mem hf)) he).trans ha

theorem Trace.memory_frame {p stop n s t} (h : Trace p stop n s t)
    (hw : ∀ i ∈ p.code, writesMemory i = false) : t.memory = s.memory := by
  apply h.invariant (P := fun u => u.memory = s.memory) rfl
  intro a b ha hs
  unfold step at hs
  cases hf : p.fetch a.pc with
  | error e => simp [hf, bind, Except.bind] at hs
  | ok i =>
    have he : execInstr i a = .ok b := by simpa [hf, bind, Except.bind] using hs
    exact (execInstr_memory_frame (hw i (fetch_mem hf)) he).trans ha

end Libp2pAsm.Rv64.Logic
