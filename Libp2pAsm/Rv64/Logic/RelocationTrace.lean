import Libp2pAsm.Rv64.Logic.RelocationAddress

namespace Libp2pAsm.Rv64.Logic

set_option backward.isDefEq.respectTransparency false

/-- Finite structural obligations on the source image, independent of any execution. -/
structure LeafLayout (p : Program) : Prop where
  positive : 0 < p.base.toNat
  aligned : p.base.toNat % 4 = 0
  bounded : p.base.toNat + 4*p.code.size ≤ 2^64
  instr : ∀ j : Fin p.code.size, LeafInstr p.code[j]
  targets : ∀ j : Fin p.code.size, AvoidsZero (codeAddress p j) p.code[j]

/-- Relocation permits base zero and every aligned return address outside this leaf,
including addresses of other instructions in a containing program. -/
structure Placement (p : Program) (base ra : Word) : Prop where
  aligned : base.toNat % 4 = 0
  bounded : base.toNat + 4*p.code.size ≤ 2^64
  returnAligned : ra.toNat % 4 = 0
  external : ra.toNat < base.toNat ∨ base.toNat + 4*p.code.size ≤ ra.toNat

def relocated (p : Program) (base : Word) : Program := { p with base := base }

def relocateState (p : Program) (base ra : Word) (s : State) : State :=
  remap (relocatePC (base-p.base) ra) ra s

theorem LeafInstr.destination {i : Instr} (h : LeafInstr i) : .x1 ≠ destination i := by
  cases i <;> simp_all [LeafInstr, Logic.destination]
  all_goals first | exact Ne.symm h.1 | exact Ne.symm h

theorem LeafLayout.fetched {p : Program} (h : LeafLayout p) {pc : Word} {i : Instr}
    (hf : p.fetch pc = .ok i) : LeafInstr i ∧ AvoidsZero pc i := by
  obtain ⟨j, hj, rfl, rfl⟩ := fetch_index hf h.aligned
  exact ⟨h.instr ⟨j, hj⟩, h.targets ⟨j, hj⟩⟩

theorem Placement.fetch {p : Program} {base ra pc : Word} {i : Instr}
    (hl : LeafLayout p) (hp : Placement p base ra) (hf : p.fetch pc = .ok i) :
    (relocated p base).fetch (relocatePC (base-p.base) ra pc) = .ok i ∧
      relocatePC (base-p.base) ra pc ≠ ra := by
  obtain ⟨j, hj, rfl, he⟩ := fetch_index hf hl.aligned
  have hz := codeAddress_nonzero hl.positive hl.bounded hj
  have hm : relocatePC (base-p.base) ra (codeAddress p j) = codeAddress (relocated p base) j := by
    simpa only [relocatePC, hz, ↓reduceIte, relocated] using codeAddress_relocate p base j
  rw [hm]
  constructor
  · rw [fetch_codeAddress (relocated p base) j hj hp.aligned hp.bounded]; exact congrArg Except.ok he
  · have hi : InCode (relocated p base) (codeAddress (relocated p base) j) :=
      fetch_inCode (fetch_codeAddress (relocated p base) j hj hp.aligned hp.bounded)
    intro heq
    rw [heq] at hi
    have he := hp.external
    simp only [InCode, relocated] at hi
    omega

theorem relocate_exec {p : Program} {base ra : Word} {s t : State} {i : Instr}
    (hl : LeafLayout p) (hp : Placement p base ra) (hf : p.fetch s.pc = .ok i)
    (hr : s.getReg .x1 = 0) (he : execInstr i s = .ok t) :
    execInstr i (relocateState p base ra s) = .ok (relocateState p base ra t) := by
  obtain ⟨hi, hz⟩ := hl.fetched hf
  have hs : s.pc ≠ 0 := by
    have hc := fetch_inCode hf
    intro heq
    rw [heq] at hc
    have := hl.positive
    simp [InCode] at hc
    omega
  exact execInstr_remap hi
    (relocatePC_instr _ _ _ i hs (sub_aligned _ _ hp.aligned hl.aligned) hz)
    (relocatePC_zero _ _) hp.returnAligned hr he

theorem Trace.relocate {p : Program} {base ra : Word} {n : Nat} {s t : State}
    (h : Trace p 0 n s t) (hl : LeafLayout p) (hp : Placement p base ra)
    (hr : s.getReg .x1 = 0) :
    Trace (relocated p base) ra n (relocateState p base ra s) (relocateState p base ra t) := by
  induction h with
  | nil => exact .nil _
  | @cons n s a t hn hs tail ih =>
    unfold step at hs
    cases hf : p.fetch s.pc with
    | error e => simp [hf, bind, Except.bind] at hs
    | ok i =>
      have he : execInstr i s = .ok a := by simpa [hf, bind, Except.bind] using hs
      have hara : a.getReg .x1 = 0 :=
        (execInstr_register_frame (hl.fetched hf).1.destination he).trans hr
      exact .cons (hp.fetch hl hf).2
        (step_of_fetch (hp.fetch hl hf).1 (relocate_exec hl hp hf hr he)) (ih hara)

theorem WritesWithin.remap {f : Word → Word} {ra : Word} {lo hi : Nat} {i : Instr} {s : State}
    (hl : LeafInstr i) (hw : WritesWithin lo hi i s) : WritesWithin lo hi i (remap f ra s) := by
  cases i <;> simp only [WritesWithin] at hw ⊢ <;> try trivial
  all_goals simpa only [remap_get _ _ _ _ hl.1] using hw

theorem WriteTrace.relocate {p : Program} {base ra : Word} {lo hi n : Nat} {s t : State}
    (h : WriteTrace p 0 lo hi n s t) (hl : LeafLayout p) (hp : Placement p base ra)
    (hr : s.getReg .x1 = 0) :
    WriteTrace (relocated p base) ra lo hi n
      (relocateState p base ra s) (relocateState p base ra t) := by
  induction h with
  | nil => exact .nil _
  | cons hn hf he hw tail ih =>
    have hara := (execInstr_register_frame (hl.fetched hf).1.destination he).trans hr
    exact .cons (hp.fetch hl hf).2 (hp.fetch hl hf).1 (relocate_exec hl hp hf hr he)
      (hw.remap (hl.fetched hf).1) (ih hara)

end Libp2pAsm.Rv64.Logic
