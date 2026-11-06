import Libp2pAsm.Rv64.State

namespace Libp2pAsm.Rv64

@[simp] theorem State.getReg_zero (s : State) : s.getReg .x0 = 0 := by
  simp [getReg]

@[simp] theorem State.setReg_zero (s : State) (value : Word) :
    s.setReg .x0 value = s := by
  simp [setReg]

theorem State.getReg_setReg_same (s : State) (r : Reg) (value : Word) (h : r ≠ .x0) :
    (s.setReg r value).getReg r = value := by
  simp [getReg, setReg, h]

theorem State.getReg_setReg_other (s : State) (written read : Reg) (value : Word)
    (h : read.toNat ≠ written.toNat) :
    (s.setReg written value).getReg read = s.getReg read := by
  by_cases hw : written = .x0
  · simp [setReg, hw]
  by_cases hr : read = .x0
  · simp [hr]
  simp [getReg, setReg, hw, hr, Ne.symm h]

@[simp] theorem State.getReg_advance (s : State) (r : Reg) :
    s.advance.getReg r = s.getReg r := rfl

@[simp] theorem State.memory_setReg (s : State) (r : Reg) (value : Word) :
    (s.setReg r value).memory = s.memory := by
  by_cases h : r = .x0 <;> simp [setReg, h]

@[simp] theorem State.pc_setReg (s : State) (r : Reg) (value : Word) :
    (s.setReg r value).pc = s.pc := by
  by_cases h : r = .x0 <;> simp [setReg, h]

end Libp2pAsm.Rv64
