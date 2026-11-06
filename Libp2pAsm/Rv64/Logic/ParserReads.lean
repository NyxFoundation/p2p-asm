import Libp2pAsm.Rv64.Logic.ParserSymbolic
import Libp2pAsm.Rv64.Logic.RelocationTrace

namespace Libp2pAsm.Rv64.Logic.Parser

/-- Exact load addresses and widths, as opposed to just memory equality. -/
def loads (i : Instr) (s : State) : List (Nat × Word) :=
  match i with
  | .LBU _ a off => [(1,s.getReg a+off.signExtend 64)]
  | .LD _ a off => [(8,s.getReg a+off.signExtend 64)]
  | _ => []

inductive ReadTrace (p : Program) (stop : Word) : List (Nat × Word) → Nat → State → State → Prop
  | nil (s) : ReadTrace p stop [] 0 s s
  | cons {n s t u i accesses rest} : s.pc ≠ stop → p.fetch s.pc = .ok i →
      execInstr i s = .ok t → accesses = loads i s ++ rest →
      ReadTrace p stop rest n t u → ReadTrace p stop accesses (n+1) s u

theorem ReadTrace.trace {p stop accesses n s t} (h : ReadTrace p stop accesses n s t) :
    Trace p stop n s t := by
  induction h with
  | nil => exact .nil _
  | cons hn hf he _ _ ih => exact .cons hn (step_of_fetch hf he) ih

theorem ReadTrace.append {p stop left right n m s t u}
    (h : ReadTrace p stop left n s t) (k : ReadTrace p stop right m t u) :
    ReadTrace p stop (left++right) (n+m) s u := by
  induction h with
  | nil => simpa using k
  | cons hn hf he hl _ ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ReadTrace.cons hn hf he (by rw [hl,List.append_assoc]) (ih k)

theorem readTrace_at_pc {p stop accesses n s t pc} (hp : s.pc = pc)
    (h : ReadTrace p stop accesses n (atPC s pc) t) : ReadTrace p stop accesses n s t := by
  simpa only [←hp,atPC_self] using h

theorem ReadTrace.prefix_load {p stop accesses n s t} (h : ReadTrace p stop accesses n s t)
    {k u i} (hk : k < n) (hp : Trace p stop k s u) (hf : p.fetch u.pc = .ok i) :
    ∀ a ∈ loads i u, a ∈ accesses := by
  induction h generalizing k u with
  | nil => omega
  | @cons n s a t j reads rest hn hj he hl ht ih =>
    cases hp with
    | nil =>
      have hij : i=j := Except.ok.inj (hf.symm.trans hj)
      subst i
      intro x hx; rw [hl]; exact List.mem_append_left _ hx
    | @cons k _ b u _ hs tail =>
      have hab : a=b := Except.ok.inj ((step_of_fetch hj he).symm.trans hs)
      subst b
      intro x hx; rw [hl]
      exact List.mem_append_right _ (ih (by omega) tail hf x hx)

theorem loads_remap {f : Word → Word} {ra : Word} {i : Instr} {s : State}
    (hl : LeafInstr i) : loads i (remap f ra s) = loads i s := by
  cases i <;> simp only [loads] <;> try rfl
  all_goals rw [remap_get _ _ _ _ hl.2]

theorem ReadTrace.relocate {p : Program} {base ra : Word} {accesses n s t}
    (h : ReadTrace p 0 accesses n s t) (hl : LeafLayout p) (hp : Placement p base ra)
    (hr : s.getReg .x1 = 0) :
    ReadTrace (relocated p base) ra accesses n
      (relocateState p base ra s) (relocateState p base ra t) := by
  induction h with
  | nil => exact .nil _
  | cons hn hf he ha ht ih =>
    have hi := (hl.fetched hf).1
    have hara := (execInstr_register_frame hi.destination he).trans hr
    refine .cons (hp.fetch hl hf).2 (hp.fetch hl hf).1 (relocate_exec hl hp hf hr he) ?_ (ih hara)
    simpa only [relocateState,loads_remap hi] using ha

theorem ReadTrace.embed {whole leaf : Program} {start stop accesses n s t}
    (h : ReadTrace leaf stop accesses n s t) (hc : CodeSlice whole leaf start)
    (ha : whole.base.toNat % 4 = 0) (hb : whole.base.toNat+4*whole.code.size ≤ 2^64) :
    ReadTrace whole stop accesses n s t := by
  induction h with
  | nil => exact .nil _
  | cons hn hf he hr _ ih => exact .cons hn (hc.fetch ha hb hf) he hr ih

end Libp2pAsm.Rv64.Logic.Parser

open Libp2pAsm.Rv64 Libp2pAsm.Rv64.Logic Libp2pAsm.Rv64.Logic.Parser in
macro "parser_read_step" : tactic => `(tactic| (
  apply ReadTrace.cons
  · simp [advance_eq_atPC]
  · simp only [advance_eq_atPC, pc_atPC, State.pc_setReg]
    conv => lhs; cbv
    try rfl
  · simp [execInstr, loadReg, bind, Except.bind, pure, Except.pure,
      writeReg, branch, jump_eq_atPC, advance_eq_atPC, getReg_setReg, *]
    <;> (try simp_all) <;> first | rfl | (split <;> first | omega | rfl)
  · simp [loads, getReg_setReg, *]
    try rfl))
