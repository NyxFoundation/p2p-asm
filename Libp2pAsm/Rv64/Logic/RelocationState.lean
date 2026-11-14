import Libp2pAsm.Rv64.Logic.Symbolic
import Libp2pAsm.Rv64.Logic.Frame

namespace Libp2pAsm.Rv64.Logic

set_option backward.isDefEq.respectTransparency false

/-- Change code addresses and restore the caller's ra; data addresses are untouched. -/
def remap (f : Word → Word) (ra : Word) (s : State) : State :=
  atPC (s.setReg .x1 ra) (f s.pc)

@[simp] theorem remap_pc (f : Word → Word) (ra : Word) (s : State) :
    (remap f ra s).pc = f s.pc := by simp [remap]

@[simp] theorem remap_memory (f : Word → Word) (ra : Word) (s : State) :
    (remap f ra s).memory = s.memory := by simp [remap]

@[simp] theorem remap_get (f : Word → Word) (ra : Word) (s : State) (r : Reg)
    (hr : r ≠ .x1) : (remap f ra s).getReg r = s.getReg r := by
  by_cases hz : r = .x0 <;> simp [remap, getReg_setReg, hr, hz]

@[simp] theorem remap_ra (f : Word → Word) (ra : Word) (s : State) :
    (remap f ra s).getReg .x1 = ra := by simp [remap, getReg_setReg]

@[simp] theorem remap_atPC (f : Word → Word) (ra : Word) (s : State) (pc : Word) :
    remap f ra (atPC s pc) = atPC (remap f ra s) (f pc) := by simp [remap]

theorem setReg_ra_comm (s : State) (r : Reg) (v ra : Word) (hr : r ≠ .x1) :
    (s.setReg r v).setReg .x1 ra = (s.setReg .x1 ra).setReg r v := by
  cases r <;> simp_all [LeanAsm.Rv64.State.setReg, LeanAsm.Rv64.Reg.toNat, Vector.set_comm]

@[simp] theorem remap_setReg (f : Word → Word) (ra : Word) (s : State)
    (r : Reg) (v : Word) (hr : r ≠ .x1) :
    remap f ra (s.setReg r v) = (remap f ra s).setReg r v := by
  simp [remap, setReg_ra_comm s r v ra hr]

@[simp] theorem remap_withMemory (f : Word → Word) (ra : Word) (s : State) (m : Memory) :
    remap f ra (withMemory s m) = withMemory (remap f ra s) m := rfl

theorem remap_writeReg {f : Word → Word} {ra : Word} {s t : State} {d : Reg} {v : Word}
    (hd : d ≠ .x1) (hn : f (s.pc + 4) = f s.pc + 4) (he : writeReg s d v = .ok t) :
    writeReg (remap f ra s) d v = .ok (remap f ra t) := by
  simp only [writeReg, Except.ok.injEq] at he
  subst t
  simp [writeReg, advance_eq_atPC, hd]
  exact congrArg _ hn.symm

theorem remap_loadReg {f : Word → Word} {ra : Word} {s t : State}
    {width : Nat} {d a : Reg} {off : BitVec 12} (hd : d ≠ .x1) (ha : a ≠ .x1)
    (hn : f (s.pc + 4) = f s.pc + 4) (he : loadReg s width d a off = .ok t) :
    loadReg (remap f ra s) width d a off = .ok (remap f ra t) := by
  simp only [loadReg, remap_memory, remap_get _ _ _ _ ha, bind, Except.bind] at *
  split at he
  · cases he
  · exact remap_writeReg hd hn he

theorem remap_storeReg {f : Word → Word} {ra : Word} {s t : State}
    {width : Nat} {a b : Reg} {off : BitVec 12} (ha : a ≠ .x1) (hb : b ≠ .x1)
    (hn : f (s.pc + 4) = f s.pc + 4) (he : storeReg s width a b off = .ok t) :
    storeReg (remap f ra s) width a b off = .ok (remap f ra t) := by
  simp only [storeReg_eq_atPC, remap_memory, remap_get _ _ _ _ ha,
    remap_get _ _ _ _ hb, bind, Except.bind, pure, Except.pure] at *
  split at he
  · cases he
  · cases he; simp; exact congrArg _ hn.symm

/-- A PC translation preserves the relative target and its alignment. -/
def MapsOffset (f : Word → Word) (pc off : Word) : Prop :=
  f (pc + off) = f pc + off ∧
    ((f (pc + off)).toNat % 4 = 0 ↔ (pc + off).toNat % 4 = 0)

theorem remap_jump {f : Word → Word} {ra : Word} {s t : State} {off : Word}
    (hm : MapsOffset f s.pc off) (he : jump s .x0 (s.pc + off) = .ok t) :
    jump (remap f ra s) .x0 ((remap f ra s).pc + off) = .ok (remap f ra t) := by
  simp only [jump_eq_atPC, State.setReg_zero, beq_iff_eq] at he ⊢
  split at he
  · rename_i ha
    cases he
    simp [← hm.1, hm.2.mpr ha]
  · cases he

theorem remap_branch {f : Word → Word} {ra : Word} {s t : State}
    {taken : Bool} {off : BitVec 13}
    (hn : f (s.pc + 4) = f s.pc + 4) (hm : MapsOffset f s.pc (off.signExtend 64))
    (he : branch s taken off = .ok t) :
    branch (remap f ra s) taken off = .ok (remap f ra t) := by
  cases taken
  · simp only [branch, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at he
    subst t
    simp [branch, advance_eq_atPC]
    exact congrArg _ hn.symm
  · exact remap_jump hm he

end Libp2pAsm.Rv64.Logic
