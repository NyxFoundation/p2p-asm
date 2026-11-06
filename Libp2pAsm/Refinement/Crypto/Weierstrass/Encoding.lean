import Libp2pAsm.Spec.Crypto.Weierstrass.Ecdsa

namespace Libp2pAsm.Refinement.Crypto.Weierstrass
open Spec.Crypto.Weierstrass

theorem encodePoint_length (compressed : Bool) (p : Affine) :
    (encodePoint compressed p).length = if compressed then 33 else 65 := by
  cases compressed <;> simp [encodePoint, writeBE]

theorem parseCompact_valid (c : Curve) (low : Bool) (bytes : List UInt8) (s : Signature)
    (h : parseCompact c low bytes = some s) : validSignature c low s = true := by
  dsimp [parseCompact] at h
  split at h
  next valid =>
    cases h
    simp at valid
    exact valid.2
  next => contradiction

theorem parseCompact_length (c : Curve) (low : Bool) (bytes : List UInt8) (s : Signature)
    (h : parseCompact c low bytes = some s) : bytes.length = 64 := by
  dsimp [parseCompact] at h
  split at h
  next valid =>
    simp at valid
    exact valid.1
  next => contradiction

theorem scalar_domain (c : Curve) (n : Nat) (h : validScalar c n = true) :
    1 ≤ n ∧ n < c.order := by
  simp [validScalar] at h
  omega

theorem signature_domain (c : Curve) (low : Bool) (s : Signature)
    (h : validSignature c low s = true) :
    1 ≤ s.r ∧ s.r < c.order ∧ 1 ≤ s.s ∧ s.s < c.order := by
  simp [validSignature, validScalar] at h
  omega

theorem lowS_domain (c : Curve) (s : Signature) (h : validSignature c true s = true) :
    s.s ≤ c.order/2 := by
  simp [validSignature] at h
  exact h.2

theorem parseDER_canonical (c : Curve) (low : Bool) (bytes : List UInt8) (s : Signature)
    (h : parseDER c low bytes = some s) : validSignature c low s = true ∧ der s = bytes := by
  dsimp [parseDER] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  next accepted =>
    cases h
    simpa using accepted

end Libp2pAsm.Refinement.Crypto.Weierstrass
