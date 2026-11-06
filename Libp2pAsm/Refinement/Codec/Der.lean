import Libp2pAsm.Spec.Codec.Der

namespace Libp2pAsm.Refinement.Codec.Der
open Spec.Codec.Der

@[simp] private theorem throw_eq (e : Error) :
    (throw e : Except Error α) = .error e := rfl

@[simp] private theorem error_bind (e : Error) (f : α → Except Error β) :
    ((Except.error e : Except Error α) >>= f) = .error e := rfl

@[simp] private theorem pure_eq (a : α) : (pure a : Except Error α) = .ok a := rfl

/-- A successful TLV never consumes beyond its represented input. -/
theorem decode_bounds {bytes : List UInt8} {d : Decoded}
    (h : decode bytes = .ok d) :
    2 ≤ d.header ∧ d.consumed = d.header + d.length ∧ d.consumed ≤ bytes.length := by
  cases bytes with
  | nil => simp [decode] at h
  | cons tag rest =>
    cases rest with
    | nil =>
      simp [decode] at h
      split at h <;> simp_all
    | cons first tail =>
      simp [decode] at h
      repeat' (split at h <;> try simp_all)
      all_goals cases h; simp_all; omega

/-- The encoder never silently truncates an out-of-range length. -/
theorem encode_overflow {tag n : Nat} (ht : supportedTag tag = true) (hn : 2^64 ≤ n) :
    encodeHeader tag n = .error .overflow := by
  simp [encodeHeader, ht, hn]

/-- Context-specific tag zero is distinct from the forbidden end-of-contents. -/
theorem context_zero : supportedTag 0x80 = true ∧ supportedTag 0xa0 = true ∧
    supportedTag 0 = false ∧ supportedTag 0x20 = false := by decide

end Libp2pAsm.Refinement.Codec.Der
