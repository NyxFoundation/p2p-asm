import Libp2pAsm.Spec.Codec.Der

namespace Libp2pAsm.Refinement.AsmDer
open Spec.Codec.Der

theorem decode_bounds (bytes : List UInt8) (d : Decoded) (h : decode bytes=.ok d) :
    2 ≤ d.header ∧ d.header ≤ 10 ∧ d.consumed=d.header+d.length ∧ d.consumed ≤ bytes.length := by
  cases bytes with
  | nil => simp [decode] at h
  | cons tag rest =>
    cases rest with
    | nil =>
      simp [decode,throw,throwThe,MonadExceptOf.throw,bind,Except.bind] at h
      split at h <;> simp_all
    | cons first tail =>
      simp [decode,throw,throwThe,MonadExceptOf.throw,bind,Except.bind,pure,Except.pure] at h
      repeat' (split at h <;> try simp_all)
      all_goals cases h; simp_all; omega

theorem significant_length (width n : Nat) (hn : n < 256^width) :
    (significantBytes n).length ≤ width := by
  induction width generalizing n with
  | zero =>
    have : n=0 := by simp at hn; omega
    subst n
    simp [significantBytes]
  | succ width ih =>
    rw [significantBytes]
    split
    · simp
    · have hd : n/256 < 256^width := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0<256)).mpr
        simpa [Nat.pow_succ,Nat.mul_comm] using hn
      have hh := ih (n/256) hd
      simp only [List.length_append,List.length_singleton]
      omega

/-- The output bound depends only on the header, never on content allocation. -/
theorem encode_header_bound (tag length : Nat) (bytes : List UInt8)
    (h : encodeHeader tag length=.ok bytes) : 2 ≤ bytes.length ∧ bytes.length ≤ 10 := by
  simp only [encodeHeader,bind,Except.bind,pure,Except.pure,throw,throwThe,MonadExceptOf.throw] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hn
      have hh := significant_length 8 length (by simpa using (Nat.lt_of_not_ge hn))
      split at h <;> cases h <;> simp_all <;> omega

end Libp2pAsm.Refinement.AsmDer
