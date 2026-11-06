import Libp2pAsm.Refinement.AsmDer.EncodePreflight

namespace Libp2pAsm.Refinement.AsmDer.Encode
open Rv64 Rv64.Logic Rv64.Logic.Parser

theorem rawError_none (tag value ptr cap : Word) (h : rawError tag value ptr cap=none) :
    Spec.Codec.Der.supportedTag tag.toNat=true ∧ headerSize value.toNat≤cap.toNat ∧
      ptr.toNat+headerSize value.toNat≤2^64 := by
  unfold rawError boundsError at h
  repeat' (split at h <;> try cases h)
  all_goals (simp_all <;> omega)

theorem reverseWrites_member (base : Word) (offset n : Nat) (a : Nat × Word)
    (ha : a∈reverseWrites base offset n) : ∃ i, i<n ∧ a=(1,base+BitVec.ofNat 64 (offset+i)) := by
  induction n with
  | zero => simp [reverseWrites] at ha
  | succ n ih =>
    simp only [reverseWrites,List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact ⟨n,by omega,rfl⟩
    · obtain ⟨i,hi,he⟩ := ih ha
      exact ⟨i,by omega,he⟩

theorem headerWrites_member (base value : Word) (a : Nat × Word) (ha : a∈headerWrites base value) :
    ∃ i, i<headerSize value.toNat ∧ a=(1,base+BitVec.ofNat 64 i) := by
  have hb := headerSize_bounds value
  simp only [headerWrites,List.mem_cons] at ha
  rcases ha with rfl | rfl | ha
  · exact ⟨0,by omega,by simp⟩
  · exact ⟨1,by omega,by simp⟩
  · split at ha
    · simp at ha
    · rename_i hlong
      obtain ⟨i,hi,rfl⟩ := reverseWrites_member base 2 _ a ha
      exact ⟨2+i,by simp only [headerSize,if_neg hlong]; omega,rfl⟩

theorem rawWrites_bounds (tag value ptr cap : Word) (a : Nat × Word) (ha : a∈rawWrites tag value ptr cap) :
    a.1=1 ∧ ptr.toNat≤a.2.toNat ∧ a.2.toNat+1≤ptr.toNat+headerSize value.toNat := by
  unfold rawWrites at ha
  cases he : rawError tag value ptr cap with
  | some e => simp [he] at ha
  | none =>
    simp only [he] at ha
    have hb := (rawError_none tag value ptr cap he).2.2
    obtain ⟨i,hi,rfl⟩ := headerWrites_member ptr value a ha
    have hi64 : i<2^64 := by omega
    have hsum : ptr.toNat+i<2^64 := by omega
    simp [BitVec.toNat_add,Nat.mod_eq_of_lt hi64,Nat.mod_eq_of_lt hsum]
    omega

/-- A successful raw result is precisely the frozen header specification. -/
theorem result_spec (tag value ptr cap : Word) (out : List UInt8) (h : result tag value ptr cap=.ok out) :
    Spec.Codec.Der.encodeHeader tag.toNat value.toNat=.ok out ∧ out.length≤10 := by
  unfold result at h
  cases he : rawError tag value ptr cap with
  | some e => simp [he] at h
  | none =>
    simp only [he,Except.ok.injEq] at h
    subst out
    exact ⟨header_spec tag value (rawError_none tag value ptr cap he).1,
      by rw [header_length]; exact (headerSize_bounds value).2⟩

end Libp2pAsm.Refinement.AsmDer.Encode
