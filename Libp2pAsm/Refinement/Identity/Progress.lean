import Libp2pAsm.Spec.Identity.PublicKey
import Libp2pAsm.Refinement.AsmProtobuf.Specification
import Libp2pAsm.Rv64.Logic.ParserSymbolic

namespace Libp2pAsm.Refinement.Identity
open Spec.Identity.PublicKey

abbrev fieldValue := parser_internal% Libp2pAsm.Spec.Identity.PublicKey.value
abbrev lengthField := parser_internal% Libp2pAsm.Spec.Identity.PublicKey.lengthField
abbrev complete := parser_internal% Libp2pAsm.Spec.Identity.PublicKey.complete

theorem advance_accounting (s : ParseState) (n : Nat) (h : n ≤ s.rest.length) :
    (advance s n).offset+(advance s n).rest.length = s.offset+s.rest.length ∧
      (advance s n).offset = s.offset+n ∧ (advance s n).rest.length = s.rest.length-n := by
  simp [advance]; omega

theorem read_progress (s t : ParseState) (n : Nat)
    (h : readVarint s = .ok (n,t)) :
    t.rest.length < s.rest.length ∧ t.offset+t.rest.length = s.offset+s.rest.length ∧
      s.offset < t.offset ∧ t.groups = s.groups ∧ t.kind = s.kind ∧ t.data = s.data := by
  cases hd : Spec.Codec.ProtobufVarint.decode s.rest with
  | error e => simp [readVarint, hd, Except.mapError, bind, Except.bind] at h
  | ok d =>
    have hb := AsmProtobuf.decode_consumed s.rest d hd
    simp [readVarint, hd, Except.mapError, bind, Except.bind, pure, Except.pure] at h
    obtain ⟨rfl,rfl⟩ := h
    simp [advance]; omega

theorem skip_progress (s t : ParseState) (n : Nat) (h : skip s n = .ok t) :
    t.rest.length ≤ s.rest.length ∧ t.offset+t.rest.length = s.offset+s.rest.length ∧
      s.offset ≤ t.offset ∧ t.groups = s.groups ∧ t.kind = s.kind ∧ t.data = s.data := by
  unfold skip at h
  split at h
  · cases h
  · cases h
    simp [advance]; omega

theorem length_progress (s t : ParseState) (field : Nat)
    (h : lengthField s field = .ok t) :
    t.rest.length ≤ s.rest.length ∧ t.offset+t.rest.length = s.offset+s.rest.length ∧
      s.offset ≤ t.offset ∧ t.groups = s.groups := by
  unfold lengthField at h
  parser_unfold Libp2pAsm.Spec.Identity.PublicKey.lengthField at h
  cases hr : readVarint s with
  | error e => simp [hr, bind, Except.bind] at h
  | ok pair =>
    obtain ⟨n,a⟩ := pair
    cases hs : skip a n with
    | error e => simp [hr, hs, bind, Except.bind] at h
    | ok b =>
      obtain ⟨hp1,hp2,hp3,hp4,hp5,hp6⟩ := read_progress s a n hr
      obtain ⟨hq1,hq2,hq3,hq4,hq5,hq6⟩ := skip_progress a b n hs
      simp only [hr, hs, bind, Except.bind, pure, Except.pure] at h
      split at h <;> cases h <;> simp_all <;> omega

/-- Even mismatched known wire types follow the unknown-field path. -/
theorem value_progress (s t : ParseState) (field wire : Nat)
    (h : fieldValue s field wire = .ok t) :
    t.rest.length ≤ s.rest.length ∧ t.offset+t.rest.length = s.offset+s.rest.length ∧
      s.offset ≤ t.offset ∧ t.groups.length ≤ s.groups.length+1 := by
  unfold fieldValue at h
  parser_unfold Libp2pAsm.Spec.Identity.PublicKey.value at h
  split at h
  · cases hr : readVarint s with
    | error e => simp [hr, bind, Except.bind] at h
    | ok pair =>
      obtain ⟨n,a⟩ := pair
      have hp := read_progress s a n hr
      simp only [hr, bind, Except.bind, pure, Except.pure] at h
      split at h <;> cases h <;> simp_all <;> omega
  · have hp := skip_progress _ _ _ h; simp_all <;> omega
  · have hp := length_progress _ _ _ h; simp_all <;> omega
  · cases h; simp
  · split at h
    · split at h
      · cases h
      · cases h; simp_all <;> omega
    · cases h
  · have hp := skip_progress _ _ _ h; simp_all <;> omega
  · cases h

end Libp2pAsm.Refinement.Identity
