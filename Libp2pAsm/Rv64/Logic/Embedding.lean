import Libp2pAsm.Rv64.Logic.Fetch
import Libp2pAsm.Rv64.Logic.WriteTrace

namespace Libp2pAsm.Rv64.Logic

/-- A checked instruction subarray; the surrounding program may contain arbitrary code. -/
structure CodeSlice (whole leaf : Program) (start : Nat) : Prop where
  fits : start + leaf.code.size ≤ whole.code.size
  base : leaf.base.toNat = whole.base.toNat + 4 * start
  code : ∀ j (hj : j < leaf.code.size),
    whole.code[start + j]'(by omega) = leaf.code[j]

theorem CodeSlice.refl (p : Program) : CodeSlice p p 0 := by
  exact ⟨by omega, by omega, by intro j hj; simp⟩

/-- An aligned instruction address strictly inside an image. -/
def InCode (p : Program) (pc : Word) : Prop :=
  pc.toNat % 4 = 0 ∧ p.base.toNat ≤ pc.toNat ∧
    pc.toNat < p.base.toNat + 4 * p.code.size

theorem fetch_inCode {p : Program} {pc : Word} {i : Instr}
    (hf : p.fetch pc = .ok i) : InCode p pc := by
  simp only [Program.fetch, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at hf
  repeat split at hf
  all_goals simp_all [InCode]
  omega

theorem fetch_index {p : Program} {pc : Word} {i : Instr}
    (hf : p.fetch pc = .ok i) (ha : p.base.toNat % 4 = 0) :
    ∃ j, ∃ hj : j < p.code.size, pc = codeAddress p j ∧ p.code[j] = i := by
  have hi := fetch_inCode hf
  let j := (pc.toNat - p.base.toNat) / 4
  have hj : j < p.code.size := by dsimp [j]; rcases hi with ⟨_, _, _⟩; omega
  refine ⟨j, hj, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [codeAddress, BitVec.toNat_ofNat]
    have hn : p.base.toNat + 4 * j = pc.toNat := by
      dsimp [j]; rcases hi with ⟨_, _, _⟩; omega
    rw [hn, Nat.mod_eq_of_lt pc.isLt]
  · simpa [Program.fetch, hi.1, hi.2.1, j, hj, pure, Except.pure] using hf

theorem CodeSlice.fetch {whole leaf : Program} {start : Nat}
    (h : CodeSlice whole leaf start) (ha : whole.base.toNat % 4 = 0)
    (hb : whole.base.toNat + 4 * whole.code.size ≤ 2^64)
    {pc : Word} {i : Instr} (hf : leaf.fetch pc = .ok i) :
    whole.fetch pc = .ok i := by
  have hla : leaf.base.toNat % 4 = 0 := by rw [h.base]; omega
  obtain ⟨j, hj, rfl, he⟩ := fetch_index hf hla
  have hp : codeAddress leaf j = codeAddress whole (start + j) := by
    simp [codeAddress, h.base]; congr 1; omega
  rw [hp, fetch_codeAddress whole (start+j) (by have := h.fits; omega) ha hb,
    h.code j hj, he]

theorem Trace.prefix_inCode {p stop n s t} (h : Trace p stop n s t)
    {k u} (hk : k < n) (hprefix : Trace p stop k s u) : InCode p u.pc := by
  induction h generalizing k u with
  | nil => omega
  | @cons n s a t hn hs tail ih =>
    cases hprefix with
    | nil =>
      unfold step at hs
      cases hf : p.fetch s.pc with
      | error e => simp [hf, bind, Except.bind] at hs
      | ok i => exact fetch_inCode hf
    | @cons k _ b u _ he rest =>
      have hab := Except.ok.inj (hs.symm.trans he)
      subst b
      exact ih (by omega) rest

theorem Trace.embed {whole leaf : Program} {start stop n s t}
    (h : Trace leaf stop n s t) (hc : CodeSlice whole leaf start)
    (ha : whole.base.toNat % 4 = 0)
    (hb : whole.base.toNat + 4 * whole.code.size ≤ 2^64) :
    Trace whole stop n s t := by
  induction h with
  | nil => exact .nil _
  | @cons n s a t hn hs tail ih =>
    unfold step at hs
    cases hf : leaf.fetch s.pc with
    | error e => simp [hf, bind, Except.bind] at hs
    | ok i =>
      apply Trace.cons hn (step_of_fetch (hc.fetch ha hb hf) ?_) ih
      simpa [hf, bind, Except.bind] using hs

theorem WriteTrace.embed {whole leaf : Program} {start stop lo hi n s t}
    (h : WriteTrace leaf stop lo hi n s t) (hc : CodeSlice whole leaf start)
    (ha : whole.base.toNat % 4 = 0)
    (hb : whole.base.toNat + 4 * whole.code.size ≤ 2^64) :
    WriteTrace whole stop lo hi n s t := by
  induction h with
  | nil => exact .nil _
  | cons hn hf he hw tail ih => exact .cons hn (hc.fetch ha hb hf) he hw ih

/-- Every proper execution prefix of the containing program still fetches in the
leaf. Unrelated code, including the return continuation, is never fetched. -/
theorem Trace.embed_prefix_inCode {whole leaf : Program} {start stop n s t}
    (h : Trace leaf stop n s t) (hc : CodeSlice whole leaf start)
    (ha : whole.base.toNat % 4 = 0)
    (hb : whole.base.toNat + 4 * whole.code.size ≤ 2^64)
    {k u} (hk : k < n) (hprefix : Trace whole stop k s u) : InCode leaf u.pc := by
  induction h generalizing k u with
  | nil => omega
  | @cons n s a t hn hs tail ih =>
    unfold step at hs
    cases hf : leaf.fetch s.pc with
    | error e => simp [hf, bind, Except.bind] at hs
    | ok i =>
      have he : execInstr i s = .ok a := by simpa [hf, bind, Except.bind] using hs
      cases hprefix with
      | nil => exact fetch_inCode hf
      | @cons k _ b u _ hstep rest =>
        have hab := Except.ok.inj ((step_of_fetch (hc.fetch ha hb hf) he).symm.trans hstep)
        subst b
        exact ih (by omega) rest

/-- Explicit non-wrapping executable image and writable-code separation.
Memory validity includes ownership, nonempty regions and disjoint mappings. -/
structure ValidImage (p : Program) (m : Memory) : Prop where
  memory : m.valid = true
  aligned : p.base.toNat % 4 = 0
  nonempty : 0 < p.code.size
  bounded : p.base.toNat + 4*p.code.size ≤ 2^64
  separated : ∀ r ∈ m.regions, r.writable = true →
    r.endAddr ≤ p.base.toNat ∨ p.base.toNat + 4*p.code.size ≤ r.base.toNat

theorem ValidImage.valid {p : Program} {m : Memory} (h : ValidImage p m) :
    p.valid m = true := by
  simp only [Program.valid, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨h.memory, h.aligned, h.nonempty, h.bounded⟩, ?_⟩
  rw [Array.all_eq_true]
  intro j hj
  cases hw : m.regions[j].writable with
  | false => simp
  | true => simp [h.separated m.regions[j] (Array.getElem_mem hj) hw]

end Libp2pAsm.Rv64.Logic
