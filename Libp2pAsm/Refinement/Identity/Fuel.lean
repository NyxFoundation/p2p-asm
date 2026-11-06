import Libp2pAsm.Refinement.Identity.Progress

namespace Libp2pAsm.Refinement.Identity
open Spec.Identity.PublicKey

set_option maxRecDepth 8192

theorem iteration_progress (s a t : ParseState) (tag : Nat)
    (hr : readVarint s = .ok (tag,a))
    (hv : fieldValue a (tag/8) (tag%8) = .ok t) :
    t.rest.length < s.rest.length ∧ t.offset+t.rest.length = s.offset+s.rest.length := by
  obtain ⟨hr1,hr2,hr3,hr4,hr5,hr6⟩ := read_progress s a tag hr
  obtain ⟨hv1,hv2,hv3,hv4⟩ := value_progress a t (tag/8) (tag%8) hv
  omega

/-- No finite input can exhaust its byte-count fuel while input remains. -/
theorem fuel_irrelevant (fuel other : Nat) (s : ParseState)
    (hf : s.rest.length ≤ fuel) (hg : s.rest.length ≤ other) :
    parse fuel s = parse other s := by
  induction fuel generalizing s other with
  | zero =>
    have he : s.rest.isEmpty = true := by cases hh : s.rest <;> simp_all
    cases other <;> simp [parse, he, pure, Except.pure]
  | succ fuel ih =>
    by_cases he : s.rest.isEmpty = true
    · cases other <;> simp [parse, he, pure, Except.pure]
    · have hn : 0 < s.rest.length := by
        cases h : s.rest <;> simp_all
      cases other with
      | zero => omega
      | succ other =>
        cases hr : readVarint s with
        | error e => simp [parse, he, hr, bind, Except.bind]
        | ok pair =>
          obtain ⟨tag,a⟩ := pair
          by_cases ht : tag < 8 ∨ 4294967296 ≤ tag
          · simp [parse, he, hr, bind, Except.bind, ht, throw, throwThe, MonadExceptOf.throw]
          · cases hv : fieldValue a (tag/8) (tag%8) with
            | error e => simpa [parse, he, hr, bind, Except.bind, ht, hv]
            | ok t =>
              have hp := (iteration_progress s a t tag hr hv).1
              have result := ih other t (by omega) (by omega)
              simpa [parse, he, hr, bind, Except.bind, ht, hv] using result

theorem decode_fuel (bytes : List UInt8) (extra : Nat) (hb : bytes.length < 2^61) :
    decode bytes = parse (bytes.length+extra) { rest := bytes } := by
  simp only [decode, show ¬bytes.length ≥ 2^61 by omega, ↓reduceIte]
  exact fuel_irrelevant _ _ _ (by simp) (by simp)

/-- The tag is consumed before a start-group can push one word. -/
theorem groups_fit (s a t : ParseState) (tag total : Nat)
    (hs : s.offset+s.rest.length = total) (hdepth : s.groups.length ≤ s.offset)
    (hr : readVarint s = .ok (tag,a))
    (hv : fieldValue a (tag/8) (tag%8) = .ok t) :
    t.groups.length ≤ t.offset ∧ t.offset ≤ total ∧ 8*t.groups.length ≤ 8*total := by
  obtain ⟨hr1,hr2,hr3,hr4,hr5,hr6⟩ := read_progress s a tag hr
  obtain ⟨hv1,hv2,hv3,hv4⟩ := value_progress a t (tag/8) (tag%8) hv
  have hd : t.groups.length ≤ s.groups.length+1 := by simpa [hr4] using hv4
  omega

theorem group_push_capacity (s a : ParseState) (tag total : Nat)
    (hs : s.offset+s.rest.length = total) (hdepth : s.groups.length ≤ s.offset)
    (hr : readVarint s = .ok (tag,a)) : 8*a.groups.length+8 ≤ 8*total := by
  obtain ⟨hr1,hr2,hr3,hr4,hr5,hr6⟩ := read_progress s a tag hr
  rw [hr4]
  omega

theorem work_size_nonwrap (len : Nat) (h : len < 2^61) : 8*len < 2^64 := by omega

end Libp2pAsm.Refinement.Identity
