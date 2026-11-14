import Libp2pAsm.Rv64.Logic.RelocationState

namespace Libp2pAsm.Rv64.Logic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Leaf instructions may neither consume nor overwrite ra, except for the ABI return.
PC-relative data and link-register writes require a different relocation theorem. -/
def LeafInstr : Instr → Prop
  | .ADD d a b | .SUB d a b | .AND d a b | .OR d a b | .XOR d a b
  | .SLL d a b | .SRL d a b | .SRA d a b | .SLT d a b | .SLTU d a b
  | .MUL d a b | .MULHU d a b | .DIVU d a b | .REMU d a b =>
      d ≠ .x1 ∧ a ≠ .x1 ∧ b ≠ .x1
  | .ADDI d a _ | .ANDI d a _ | .ORI d a _ | .XORI d a _
  | .SLLI d a _ | .SRLI d a _ | .SRAI d a _ | .LBU d a _ | .LD d a _ =>
      d ≠ .x1 ∧ a ≠ .x1
  | .LUI d _ => d ≠ .x1
  | .SB a b _ | .SD a b _ | .BEQ a b _ | .BNE a b _
  | .BLTU a b _ | .BGEU a b _ => a ≠ .x1 ∧ b ≠ .x1
  | .JAL d _ => d = .x0
  | .JALR d a off => d = .x0 ∧ a = .x1 ∧ off = 0
  | .AUIPC .. => False
  | _ => False

instance (i : Instr) : Decidable (LeafInstr i) := by cases i <;> unfold LeafInstr <;> infer_instance

/-- Only the offsets actually present in an instruction need commute with the PC map. -/
def MapsInstr (f : Word → Word) (pc : Word) : Instr → Prop
  | .BEQ _ _ off | .BNE _ _ off | .BLTU _ _ off | .BGEU _ _ off =>
      f (pc + 4) = f pc + 4 ∧ MapsOffset f pc (off.signExtend 64)
  | .JAL _ off => MapsOffset f pc (off.signExtend 64)
  | .JALR .. => True
  | _ => f (pc + 4) = f pc + 4

theorem aligned_clear_low_bit (ra : Word) (ha : ra.toNat % 4 = 0) :
    ra &&& (~~~(1 : Word)) = ra := by
  have hlow : ra &&& 3 = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and]
    change ra.toNat &&& 3 = 0
    rw [show (3 : Nat) = 2^2-1 by decide, Nat.and_two_pow_sub_one_eq_mod]
    exact ha
  have hbit : ra[0] = false := by
    have he := congrArg (fun x : Word => x[0]) hlow
    simpa using he
  ext i hi
  by_cases hz : i = 0
  · subst i; simp [hbit]
  · simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.ofNat_eq_ofNat,
      BitVec.getElem_one, hz, decide_false, Bool.not_false, Bool.and_true]

theorem remap_return {f : Word → Word} {ra : Word} {s t : State}
    (hzero : f 0 = ra) (ha : ra.toNat % 4 = 0) (hr : s.getReg .x1 = 0)
    (he : execInstr (.JALR .x0 .x1 0) s = .ok t) :
    execInstr (.JALR .x0 .x1 0) (remap f ra s) = .ok (remap f ra t) := by
  simp [execInstr, jump_eq_atPC, hr] at he
  subst t
  have hoff : (0#12).signExtend 64 = 0#64 := by decide
  simp only [BitVec.ofNat_eq_ofNat] at *
  simp only [execInstr, remap_ra, hoff, BitVec.add_zero]
  have hmask := aligned_clear_low_bit ra ha
  simp only [BitVec.ofNat_eq_ofNat] at hmask
  simp only [BitVec.ofNat_eq_ofNat]
  rw [hmask]
  simp only [jump_eq_atPC, ha, BEq.rfl, ↓reduceIte, State.setReg_zero, remap_atPC]
  congr 2
  exact hzero.symm

/-- Relocation changes neither arithmetic nor memory effects. No execution assumption
is imposed on the target: its successful instruction is constructed from the source. -/
theorem execInstr_remap {f : Word → Word} {ra : Word} {s t : State} {i : Instr}
    (hi : LeafInstr i) (hm : MapsInstr f s.pc i) (hzero : f 0 = ra)
    (ha : ra.toNat % 4 = 0) (hr : s.getReg .x1 = 0) (he : execInstr i s = .ok t) :
    execInstr i (remap f ra s) = .ok (remap f ra t) := by
  cases i with
  | ADD d a b | SUB d a b | AND d a b | OR d a b | XOR d a b
  | SLL d a b | SRL d a b | SRA d a b | SLT d a b | SLTU d a b
  | MUL d a b | MULHU d a b | DIVU d a b | REMU d a b =>
    simp only [LeafInstr] at hi
    simp only [execInstr, remap_get _ _ _ _ hi.2.1, remap_get _ _ _ _ hi.2.2] at he ⊢
    exact remap_writeReg hi.1 hm he
  | ADDI d a off | ANDI d a off | ORI d a off | XORI d a off
  | SLLI d a off | SRLI d a off | SRAI d a off =>
    simp only [LeafInstr] at hi
    simp only [execInstr, remap_get _ _ _ _ hi.2] at he ⊢
    exact remap_writeReg hi.1 hm he
  | LUI d off => exact remap_writeReg hi hm he
  | LBU d a off | LD d a off => exact remap_loadReg hi.1 hi.2 hm he
  | SB a b off | SD a b off => exact remap_storeReg hi.1 hi.2 hm he
  | BEQ a b off | BNE a b off | BLTU a b off | BGEU a b off =>
    simp only [LeafInstr] at hi
    simp only [execInstr, remap_get _ _ _ _ hi.1, remap_get _ _ _ _ hi.2] at he ⊢
    exact remap_branch hm.1 hm.2 he
  | JAL d off =>
    change d = .x0 at hi
    subst d
    exact remap_jump hm he
  | JALR d a off =>
    rcases hi with ⟨rfl, rfl, rfl⟩
    exact remap_return hzero ha hr he
  | ADDW d a b | SUBW d a b | MULH d a b | MULHSU d a b
  | DIV d a b | REM d a b | SLTI d a off | SLTIU d a off
  | ADDIW d a off | SLLIW d a off | SRLIW d a off | FENCE =>
    exact False.elim hi
  | AUIPC _ _ => exact False.elim hi
  | _ => exact False.elim hi

end Libp2pAsm.Rv64.Logic
