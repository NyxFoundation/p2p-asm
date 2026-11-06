import Libp2pAsm.Rv64.Execution

namespace Libp2pAsm.Rv64.Logic

/-- Exact fetch/execute traces, recording that execution has not returned early. -/
inductive Trace (p : Program) (stop : Word) : Nat → State → State → Prop
  | nil (s) : Trace p stop 0 s s
  | cons {n s t u} : s.pc ≠ stop → step p s = .ok t →
      Trace p stop n t u → Trace p stop (n + 1) s u

theorem Trace.append {p stop n m s t u}
    (h : Trace p stop n s t) (k : Trace p stop m t u) :
    Trace p stop (n + m) s u := by
  induction h with
  | nil => simpa using k
  | cons hn hs _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons hn hs (ih k)

theorem Trace.runLoop {p stop n s t} (h : Trace p stop n s t)
    (ht : t.pc = stop) (extra count : Nat) :
    runLoop p stop (n + extra) s count = .ok ⟨t, count + n⟩ := by
  induction h generalizing count with
  | nil s => cases extra <;> simp [Rv64.runLoop, ht, pure, Except.pure]
  | @cons n s t u hn hs h ih =>
    rw [show n + 1 + extra = (n + extra) + 1 by omega]
    simp only [Rv64.runLoop, beq_iff_eq, hn, ↓reduceIte, hs, bind, Except.bind]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih ht (count + 1)

theorem Trace.runUntil {p stop n s t} (h : Trace p stop n s t)
    (ht : t.pc = stop) (hv : p.valid s.memory = true) (fuel : Nat) (hn : n ≤ fuel) :
    runUntil p stop fuel s = .ok ⟨t, n⟩ := by
  simpa [Rv64.runUntil, hv, Nat.add_sub_of_le hn] using h.runLoop ht (fuel - n) 0

/-- A bounded total contract. The postcondition can relate the initial and final heaps. -/
def Total (p : Program) (stop : Word) (bound : Nat)
    (pre : State → Prop) (post : State → State → Prop) : Prop :=
  ∀ s, pre s → ∃ n t, n ≤ bound ∧ Trace p stop n s t ∧
    t.pc = stop ∧ post s t

theorem Total.runUntil {p stop bound pre post} (h : Total p stop bound pre post)
    {s : State} (hs : pre s) (hv : p.valid s.memory = true) :
    ∃ done, runUntil p stop bound s = .ok done ∧ done.steps ≤ bound ∧ post s done.state := by
  obtain ⟨n, t, hn, he, ht, hp⟩ := h s hs
  exact ⟨⟨t, n⟩, he.runUntil ht hv bound hn, hn, hp⟩

theorem step_of_fetch {p : Program} {s t : State} {i : Instr}
    (hf : p.fetch s.pc = .ok i) (he : execInstr i s = .ok t) :
    step p s = .ok t := by simp [step, hf, he, bind, Except.bind]

theorem Trace.single {p stop s t i} (hn : s.pc ≠ stop)
    (hf : p.fetch s.pc = .ok i) (he : execInstr i s = .ok t) :
    Trace p stop 1 s t :=
  .cons hn (step_of_fetch hf he) (.nil t)

/-- Every intermediate state of a trace inherits a step invariant. -/
theorem Trace.invariant {p stop n s t} {P : State → Prop}
    (h : Trace p stop n s t) (hs : P s)
    (preserve : ∀ a b, P a → step p a = .ok b → P b) : P t := by
  induction h with
  | nil => exact hs
  | cons _ he _ ih => exact ih (preserve _ _ hs he)

end Libp2pAsm.Rv64.Logic
