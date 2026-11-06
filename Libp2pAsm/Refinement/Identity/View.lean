import Libp2pAsm.Refinement.Identity.Fuel

namespace Libp2pAsm.Refinement.Identity
open Spec.Identity.PublicKey

def DataWithin (s : ParseState) : Prop :=
  ∀ off len, s.data = some (off,len) → off+len ≤ s.offset

theorem read_data (s a : ParseState) (n : Nat) (hs : DataWithin s)
    (hr : readVarint s = .ok (n,a)) : DataWithin a := by
  obtain ⟨_,_,hp,_,_,hd⟩ := read_progress s a n hr
  intro off len he
  have := hs off len (hd.symm.trans he)
  omega

theorem skip_data (s a : ParseState) (n : Nat) (hs : DataWithin s)
    (hr : skip s n = .ok a) : DataWithin a := by
  obtain ⟨_,_,hp,_,_,hd⟩ := skip_progress s a n hr
  intro off len he
  have := hs off len (hd.symm.trans he)
  omega

theorem skip_offset (s a : ParseState) (n : Nat) (hr : skip s n = .ok a) :
    a.offset = s.offset+n := by
  unfold skip at hr
  split at hr
  · cases hr
  · cases hr; rfl

theorem length_data (s t : ParseState) (field : Nat) (hs : DataWithin s)
    (h : lengthField s field = .ok t) : DataWithin t := by
  unfold lengthField at h
  parser_unfold Libp2pAsm.Spec.Identity.PublicKey.lengthField at h
  cases hr : readVarint s with
  | error e => simp [hr, bind, Except.bind] at h
  | ok pair =>
    obtain ⟨n,a⟩ := pair
    cases hk : skip a n with
    | error e => simp [hr, hk, bind, Except.bind] at h
    | ok b =>
      have ha := read_data s a n hs hr
      have hb := skip_data a b n ha hk
      have ho := skip_offset a b n hk
      simp only [hr, hk, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
        intro off len he
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl,rfl⟩ := he
        exact Nat.le_of_eq ho.symm
      · cases h; exact hb

theorem value_data (s t : ParseState) (field wire : Nat) (hs : DataWithin s)
    (h : fieldValue s field wire = .ok t) : DataWithin t := by
  unfold fieldValue at h
  parser_unfold Libp2pAsm.Spec.Identity.PublicKey.value at h
  split at h
  · cases hr : readVarint s with
    | error e => simp [hr, bind, Except.bind] at h
    | ok pair =>
      obtain ⟨n,a⟩ := pair
      have hp := read_data s a n hs hr
      simp only [hr, bind, Except.bind, pure, Except.pure] at h
      split at h <;> cases h <;> exact hp
  · exact skip_data _ _ _ hs h
  · exact length_data _ _ _ hs h
  · cases h; exact hs
  · split at h
    · split at h
      · cases h
      · cases h; exact hs
    · cases h
  · exact skip_data _ _ _ hs h
  · cases h

theorem complete_view (s : ParseState) (d : View) (hs : DataWithin s)
    (h : complete s = .ok d) :
    d.offset+d.length ≤ s.offset ∧ (d.kind=1 ∨ d.kind=2) ∧ d.length=31+d.kind := by
  unfold complete at h
  parser_unfold Libp2pAsm.Spec.Identity.PublicKey.complete at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' (split at h <;> try cases h)
  all_goals simp_all [DataWithin] <;> omega

/-- Any successful parse returns a view wholly inside the original input. -/
theorem parse_view (fuel : Nat) (s : ParseState) (d : View) (hs : DataWithin s)
    (h : parse fuel s = .ok d) :
    d.offset+d.length ≤ s.offset+s.rest.length ∧
      (d.kind=1 ∨ d.kind=2) ∧ d.length=31+d.kind := by
  induction fuel generalizing s with
  | zero =>
    simp only [parse] at h
    split at h
    · have hc := complete_view s d hs h
      exact ⟨by omega,hc.2⟩
    · cases h
  | succ fuel ih =>
    by_cases he : s.rest.isEmpty = true
    · have hc := complete_view s d hs (by simpa [parse,he] using h)
      exact ⟨by omega,hc.2⟩
    cases hr : readVarint s with
    | error e => simp [parse,he,hr,bind,Except.bind] at h
    | ok pair =>
      obtain ⟨tag,a⟩ := pair
      by_cases ht : tag < 8 ∨ 4294967296 ≤ tag
      · simp [parse,he,hr,bind,Except.bind,ht,throw,throwThe,MonadExceptOf.throw] at h
      · cases hv : fieldValue a (tag/8) (tag%8) with
        | error e => simp [parse,he,hr,bind,Except.bind,ht,hv] at h
        | ok t =>
          have hd := value_data a t (tag/8) (tag%8) (read_data s a tag hs hr) hv
          have result := ih t hd (by simpa [parse,he,hr,bind,Except.bind,ht,hv] using h)
          rw [(iteration_progress s a t tag hr hv).2] at result
          exact result

theorem decode_view (bytes : List UInt8) (d : View) (h : decode bytes = .ok d) :
    d.offset+d.length ≤ bytes.length ∧ (d.kind=1 ∨ d.kind=2) ∧ d.length=31+d.kind := by
  unfold decode at h
  split at h
  · cases h
  · simpa using parse_view _ _ d (by simp [DataWithin]) h

end Libp2pAsm.Refinement.Identity
