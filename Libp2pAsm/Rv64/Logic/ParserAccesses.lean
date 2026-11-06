import Libp2pAsm.Rv64.Logic.ParserReads

namespace Libp2pAsm.Rv64.Logic.Parser

def stores (i : Instr) (s : State) : List (Nat × Word) :=
  match i with
  | .SB a _ off => [(1,s.getReg a+off.signExtend 64)]
  | .SD a _ off => [(8,s.getReg a+off.signExtend 64)]
  | _ => []

/-- An exact pair of actual load and store sequences, with no erased same-value stores. -/
inductive AccessTrace (p : Program) (stop : Word) :
    List (Nat × Word) → List (Nat × Word) → Nat → State → State → Prop
  | nil (s) : AccessTrace p stop [] [] 0 s s
  | cons {n s t u i reads writes rrest wrest} : s.pc≠stop → p.fetch s.pc=.ok i →
      execInstr i s=.ok t → reads=loads i s++rrest → writes=stores i s++wrest →
      AccessTrace p stop rrest wrest n t u → AccessTrace p stop reads writes (n+1) s u

theorem AccessTrace.readTrace {p stop reads writes n s t} (h : AccessTrace p stop reads writes n s t) :
    ReadTrace p stop reads n s t := by
  induction h with
  | nil => exact .nil _
  | cons hn hf he hr _ _ ih => exact .cons hn hf he hr ih

theorem AccessTrace.trace {p stop reads writes n s t} (h : AccessTrace p stop reads writes n s t) :
    Trace p stop n s t := h.readTrace.trace

theorem stores_within {lo hi i s}
    (h : ∀ a∈stores i s,lo≤a.2.toNat ∧ a.2.toNat+a.1≤hi) : WritesWithin lo hi i s := by
  cases i <;> simp_all [stores,WritesWithin]

theorem AccessTrace.writeTrace {p stop reads writes n s t lo hi}
    (h : AccessTrace p stop reads writes n s t)
    (hw : ∀ a∈writes,lo≤a.2.toNat ∧ a.2.toNat+a.1≤hi) : WriteTrace p stop lo hi n s t := by
  induction h with
  | nil => exact .nil _
  | cons hn hf he hr hs ht ih =>
    refine .cons hn hf he (stores_within ?_) (ih ?_)
    · intro a ha; apply hw a; rw [hs]; exact List.mem_append_left _ ha
    · intro a ha; apply hw a; rw [hs]; exact List.mem_append_right _ ha

theorem AccessTrace.append {p stop r1 r2 w1 w2 n m s t u}
    (h : AccessTrace p stop r1 w1 n s t) (k : AccessTrace p stop r2 w2 m t u) :
    AccessTrace p stop (r1++r2) (w1++w2) (n+m) s u := by
  induction h with
  | nil => simpa using k
  | cons hn hf he hr hw _ ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      AccessTrace.cons hn hf he (by rw [hr,List.append_assoc]) (by rw [hw,List.append_assoc]) (ih k)

theorem accessTrace_at_pc {p stop reads writes n s t pc} (hp : s.pc=pc)
    (h : AccessTrace p stop reads writes n (atPC s pc) t) : AccessTrace p stop reads writes n s t := by
  simpa only [←hp,atPC_self] using h

theorem AccessTrace.memory_frame {p stop reads writes n s t}
    (h : AccessTrace p stop reads writes n s t) (hw : writes=[]) : t.memory=s.memory := by
  induction h with
  | nil => rfl
  | @cons n s t u i reads writes rrest wrest hn hf he hr hs ht ih =>
    rw [hw] at hs
    have hz := (List.append_eq_nil_iff.mp hs.symm).1
    have hrest := (List.append_eq_nil_iff.mp hs.symm).2
    have hnstore : writesMemory i=false := by
      cases i <;> simp only [stores,List.cons_ne_nil] at hz <;> rfl
    exact (ih hrest).trans (execInstr_memory_frame hnstore he)

theorem stores_empty {i : Instr} {s : State} (h : writesMemory i=false) : stores i s=[] := by
  cases i <;> simp_all [stores,writesMemory]

theorem ReadTrace.noStores {p stop reads n s t} (h : ReadTrace p stop reads n s t)
    (hp : ∀ i∈p.code,writesMemory i=false) : AccessTrace p stop reads [] n s t := by
  induction h with
  | nil => exact .nil _
  | cons hn hf he hr ht ih =>
    refine .cons hn hf he hr ?_ ih
    rw [stores_empty (hp _ (fetch_mem hf))]
    rfl

theorem stores_remap {f : Word → Word} {ra : Word} {i : Instr} {s : State}
    (hl : LeafInstr i) : stores i (remap f ra s)=stores i s := by
  cases i <;> simp only [stores] <;> try rfl
  all_goals rw [remap_get _ _ _ _ hl.1]

theorem AccessTrace.relocate {p : Program} {base ra : Word} {reads writes n s t}
    (h : AccessTrace p 0 reads writes n s t) (hl : LeafLayout p) (hp : Placement p base ra)
    (hr : s.getReg .x1=0) : AccessTrace (relocated p base) ra reads writes n
      (relocateState p base ra s) (relocateState p base ra t) := by
  induction h with
  | nil => exact .nil _
  | cons hn hf he hread hw ht ih =>
    have hi := (hl.fetched hf).1
    have hara := (execInstr_register_frame hi.destination he).trans hr
    refine .cons (hp.fetch hl hf).2 (hp.fetch hl hf).1 (relocate_exec hl hp hf hr he) ?_ ?_ (ih hara)
    · simpa only [relocateState,loads_remap hi] using hread
    · simpa only [relocateState,stores_remap hi] using hw

theorem AccessTrace.embed {whole leaf : Program} {start stop reads writes n s t}
    (h : AccessTrace leaf stop reads writes n s t) (hc : CodeSlice whole leaf start)
    (ha : whole.base.toNat%4=0) (hb : whole.base.toNat+4*whole.code.size≤2^64) :
    AccessTrace whole stop reads writes n s t := by
  induction h with
  | nil => exact .nil _
  | cons hn hf he hr hw _ ih => exact .cons hn (hc.fetch ha hb hf) he hr hw ih

end Libp2pAsm.Rv64.Logic.Parser

open Libp2pAsm.Rv64 Libp2pAsm.Rv64.Logic Libp2pAsm.Rv64.Logic.Parser in
macro "parser_access_step" : tactic => `(tactic| (
  apply AccessTrace.cons
  · simp [advance_eq_atPC]
  · simp only [advance_eq_atPC,pc_atPC,State.pc_setReg]
    conv => lhs; cbv
    try rfl
  · simp [execInstr,loadReg,storeReg_eq_atPC,bind,Except.bind,pure,Except.pure,
      writeReg,branch,jump_eq_atPC,advance_eq_atPC,getReg_setReg, *]
    <;> (try simp_all) <;> first | rfl | (split <;> first | omega | rfl)
  · simp [loads,getReg_setReg, *]
    try rfl
  · simp [stores,getReg_setReg, *]
    try rfl))
