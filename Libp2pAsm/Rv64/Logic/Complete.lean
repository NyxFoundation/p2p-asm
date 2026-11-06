import Libp2pAsm.Rv64.Logic.WriteTrace

namespace Libp2pAsm.Rv64.Logic

theorem runLoop_trace {p : Program} {stop : Word} {fuel : Nat} {s : State}
    {count : Nat} {done : Completed} (h : runLoop p stop fuel s count = .ok done) :
    ∃ n, done.steps = count+n ∧ n ≤ fuel ∧ Trace p stop n s done.state ∧ done.state.pc = stop := by
  induction fuel generalizing s count with
  | zero =>
    simp only [runLoop, beq_iff_eq] at h
    split at h
    · rename_i hp; cases h; exact ⟨0, by simp, by omega, .nil _, hp⟩
    · cases h
  | succ fuel ih =>
    simp only [runLoop, beq_iff_eq] at h
    split at h
    · rename_i hp; cases h; exact ⟨0, by simp, by omega, .nil _, hp⟩
    · rename_i hp
      cases hs : step p s with
      | error e => simp [hs, bind, Except.bind] at h
      | ok t =>
        have ht : runLoop p stop fuel t (count+1) = .ok done := by
          simpa [hs, bind, Except.bind] using h
        obtain ⟨n, hn, hb, he, hr⟩ := ih ht
        exact ⟨n+1, by omega, by omega, .cons hp hs he, hr⟩

theorem Trace.noStores {p stop n s t} (h : Trace p stop n s t)
    (hw : ∀ i ∈ p.code, writesMemory i = false) (lo hi : Nat) :
    WriteTrace p stop lo hi n s t := by
  induction h with
  | nil => exact .nil _
  | @cons n s a t hn hs tail ih =>
    unfold step at hs
    cases hf : p.fetch s.pc with
    | error e => simp [hf, bind, Except.bind] at hs
    | ok i =>
      have he : execInstr i s = .ok a := by simpa [hf, bind, Except.bind] using hs
      have hw' := hw i (fetch_mem hf)
      apply WriteTrace.cons hn hf he ?_ ih
      cases i <;> simp_all [writesMemory, WritesWithin]

end Libp2pAsm.Rv64.Logic
