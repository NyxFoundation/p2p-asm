import Libp2pAsm.Rv64.Logic.Symbolic
import Libp2pAsm.Rv64.Logic.Frame

namespace Libp2pAsm.Rv64.Logic

/-- Bounds on the actual address of every store, including stores of unchanged bytes. -/
def WritesWithin (lo hi : Nat) (i : Instr) (s : State) : Prop :=
  match i with
  | .SB a _ off => lo ≤ (s.getReg a + off.signExtend 64).toNat ∧
      (s.getReg a + off.signExtend 64).toNat + 1 ≤ hi
  | .SD a _ off => lo ≤ (s.getReg a + off.signExtend 64).toNat ∧
      (s.getReg a + off.signExtend 64).toNat + 8 ≤ hi
  | .SH a _ off => lo ≤ (s.getReg a + off.signExtend 64).toNat ∧
      (s.getReg a + off.signExtend 64).toNat + 2 ≤ hi
  | .SW a _ off => lo ≤ (s.getReg a + off.signExtend 64).toNat ∧
      (s.getReg a + off.signExtend 64).toNat + 4 ≤ hi
  | _ => True

/-- A fetch/execute trace with a checked address bound at every store. -/
inductive WriteTrace (p : Program) (stop : Word) (lo hi : Nat) : Nat → State → State → Prop
  | nil (s) : WriteTrace p stop lo hi 0 s s
  | cons {n s t u i} : s.pc ≠ stop → p.fetch s.pc = .ok i → execInstr i s = .ok t →
      WritesWithin lo hi i s → WriteTrace p stop lo hi n t u →
      WriteTrace p stop lo hi (n+1) s u

theorem WriteTrace.trace {p stop lo hi n s t} (h : WriteTrace p stop lo hi n s t) :
    Trace p stop n s t := by
  induction h with
  | nil => exact .nil _
  | cons hn hf he _ _ ih => exact .cons hn (step_of_fetch hf he) ih

theorem WriteTrace.append {p stop lo hi n m s t u}
    (h : WriteTrace p stop lo hi n s t) (k : WriteTrace p stop lo hi m t u) :
    WriteTrace p stop lo hi (n+m) s u := by
  induction h with
  | nil => simpa using k
  | cons hn hf he hw _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using WriteTrace.cons hn hf he hw (ih k)

theorem writeTrace_at_pc {p stop lo hi n s t pc} (hp : s.pc = pc)
    (h : WriteTrace p stop lo hi n (atPC s pc) t) : WriteTrace p stop lo hi n s t := by
  simpa only [← hp, atPC_self] using h

/-- Any independently described execution prefix obeys the same store bound. -/
theorem WriteTrace.prefix_store {p stop lo hi n s t} (h : WriteTrace p stop lo hi n s t)
    {k u i} (hk : k < n) (hp : Trace p stop k s u) (hf : p.fetch u.pc = .ok i) :
    WritesWithin lo hi i u := by
  induction h generalizing k u with
  | nil => omega
  | @cons n s a t j hn hj he hw ht ih =>
    cases hp with
    | nil => have hij : i = j := Except.ok.inj (hf.symm.trans hj); subst i; exact hw
    | @cons k _ b u _ hs tail =>
      have hab : a = b := Except.ok.inj ((step_of_fetch hj he).symm.trans hs)
      subst b
      exact ih (by omega) tail hf

theorem WritesWithin.empty {lo i s} (h : WritesWithin lo lo i s) : writesMemory i = false := by
  cases i
  case SB rs1 rs2 off =>
    simp only [WritesWithin, writesMemory, Bool.not_eq_true] at h ⊢
    omega
  case SD rs1 rs2 off =>
    simp only [WritesWithin, writesMemory, Bool.not_eq_true] at h ⊢
    omega
  case SH rs1 rs2 off =>
    simp only [WritesWithin, writesMemory, Bool.not_eq_true] at h ⊢
    omega
  case SW rs1 rs2 off =>
    simp only [WritesWithin, writesMemory, Bool.not_eq_true] at h ⊢
    omega
  all_goals simp [writesMemory]

/-- An empty write interval rules out every store, even a store of the previous value. -/
theorem WriteTrace.empty_no_stores {p stop lo n s t} (h : WriteTrace p stop lo lo n s t)
    {k u i} (hk : k < n) (hp : Trace p stop k s u) (hf : p.fetch u.pc = .ok i) :
    writesMemory i = false := (h.prefix_store hk hp hf).empty

theorem write_address_bounds (base : Word) (offset size lo hi : Nat)
    (hb : base.toNat + size ≤ 2^64) (hoff : offset < size)
    (hl : lo ≤ base.toNat + offset) (hh : base.toNat + offset + 1 ≤ hi) :
    lo ≤ (base + BitVec.ofNat 64 offset).toNat ∧
      (base + BitVec.ofNat 64 offset).toNat + 1 ≤ hi := by
  have ho : offset < 2^64 := by omega
  have ha : base.toNat + offset < 2^64 := by omega
  simpa [BitVec.toNat_add, Nat.mod_eq_of_lt ho, Nat.mod_eq_of_lt ha] using And.intro hl hh

end Libp2pAsm.Rv64.Logic

open Libp2pAsm.Rv64 Libp2pAsm.Rv64.Logic in
macro "write_step " i:term : tactic => `(tactic| (
  apply WriteTrace.cons (i := $i)
  · simp [advance_eq_atPC]
  · simp only [advance_eq_atPC, pc_atPC, State.pc_setReg]; rfl
  · simp [execInstr, loadReg, storeReg_eq_atPC, bind, Except.bind, pure, Except.pure,
      writeReg, branch, jump_eq_atPC, advance_eq_atPC, getReg_setReg, *]
    <;> (try simp_all) <;> first | rfl | (split <;> first | omega | rfl)
  · first | trivial | (simp [WritesWithin, getReg_setReg]; assumption)))

open Libp2pAsm.Rv64 Libp2pAsm.Rv64.Logic in
macro "write_step_plain " i:term : tactic => `(tactic| (
  apply WriteTrace.cons (i := $i)
  · simp [advance_eq_atPC]
  · simp only [advance_eq_atPC, pc_atPC, State.pc_setReg]; rfl
  · simp [execInstr, writeReg, branch, jump_eq_atPC, advance_eq_atPC, getReg_setReg] <;> rfl
  · trivial))
