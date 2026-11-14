import Libp2pAsm.Refinement.Registers

namespace Libp2pAsm.Rv64.Logic

def atPC (s : State) (pc : Word) : State := { s with pc := pc }

@[simp] theorem getReg_atPC (s : State) (pc : Word) (r : Reg) :
    (atPC s pc).getReg r = s.getReg r := rfl

@[simp] theorem memory_atPC (s : State) (pc : Word) :
    (atPC s pc).memory = s.memory := rfl

@[simp] theorem pc_atPC (s : State) (pc : Word) : (atPC s pc).pc = pc := rfl

@[simp] theorem atPC_atPC (s : State) (a b : Word) : atPC (atPC s a) b = atPC s b := rfl

@[simp] theorem atPC_self (s : State) : atPC s s.pc = s := rfl

@[simp] theorem setReg_atPC (s : State) (pc : Word) (r : Reg) (v : Word) :
    (atPC s pc).setReg r v = atPC (s.setReg r v) pc := by
  cases r <;> rfl

@[simp] theorem advance_atPC (s : State) (pc : Word) :
    (atPC s pc).advance = atPC s (pc + 4) := rfl

theorem advance_eq_atPC (s : State) : s.advance = atPC s (s.pc + 4) := rfl

def withMemory (s : State) (m : Memory) : State := { s with memory := m }

@[simp] theorem getReg_withMemory (s : State) (m : Memory) (r : Reg) :
    (withMemory s m).getReg r = s.getReg r := rfl

@[simp] theorem pc_withMemory (s : State) (m : Memory) : (withMemory s m).pc = s.pc := rfl

@[simp] theorem memory_withMemory (s : State) (m : Memory) : (withMemory s m).memory = m := rfl

@[simp] theorem withMemory_atPC (s : State) (m : Memory) (pc : Word) :
    withMemory (atPC s pc) m = atPC (withMemory s m) pc := rfl

@[simp] theorem getReg_setReg (s : State) (w r : Reg) (v : Word) :
    (s.setReg w v).getReg r = if r = .x0 then 0 else if r = w then v else s.getReg r := by
  cases w <;> cases r <;> simp [LeanAsm.Rv64.State.getReg, LeanAsm.Rv64.State.setReg, LeanAsm.Rv64.Reg.toNat]

/-- Integer registers which a codec must preserve under the RISC-V ABI. -/
def CalleeSaved (r : Reg) : Prop :=
  r = .x2 ∨ r = .x8 ∨ r = .x9 ∨ r = .x18 ∨ r = .x19 ∨ r = .x20 ∨
  r = .x21 ∨ r = .x22 ∨ r = .x23 ∨ r = .x24 ∨ r = .x25 ∨ r = .x26 ∨ r = .x27

def PreservesCallee (s t : State) : Prop :=
  ∀ r, CalleeSaved r → t.getReg r = s.getReg r

theorem PreservesCallee.refl (s : State) : PreservesCallee s s := fun _ _ => rfl

theorem PreservesCallee.trans {s t u : State}
    (h : PreservesCallee s t) (k : PreservesCallee t u) : PreservesCallee s u :=
  fun r hr => (k r hr).trans (h r hr)

end Libp2pAsm.Rv64.Logic
