import Libp2pAsm.Spec.Identity.Certificate.Verify

namespace Libp2pAsm.Refinement.Identity.Certificate
open Spec.Crypto

/-- The actual ECDSA Spec decoder used by certificate authentication accepts
only the exact canonical DER re-encoding, including both scalar INTEGERs. -/
theorem ecdsa_der_canonical (curve : Weierstrass.Curve) (lowS : Bool)
    (bytes : List UInt8) (sig : Weierstrass.Signature)
    (h : Weierstrass.parseDER curve lowS bytes = some sig) :
    Weierstrass.der sig = bytes := by
  unfold Weierstrass.parseDER at h
  split at h <;> simp_all
  rcases h with ⟨_, _, ⟨_, canonical⟩, rfl⟩
  exact canonical

theorem ed_verification_lengths (key message signature : List UInt8)
    (h : Curve25519.Ed25519.verify key message signature = .ok ()) :
    key.length = 32 ∧ signature.length = 64 := by
  by_cases good : key.length = 32 ∧ signature.length = 64
  · exact good
  have hb : (key.length != 32 || signature.length != 64) = true := by
    by_cases hk : key.length = 32
    · have hs : signature.length ≠ 64 := fun hs => good ⟨hk, hs⟩
      simp [hk, hs]
    · simp [hk]
  simp [Curve25519.Ed25519.verify, hb, bind, Except.bind,
    throw, throwThe, MonadExceptOf.throw] at h

end Libp2pAsm.Refinement.Identity.Certificate
