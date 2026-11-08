import Libp2pAsm.Spec.Identity.Certificate.Issue

/-! Pure composition, domain-separation, time and grammar facts. These are NOT
whole-ASM refinement, cryptographic security, resource, or constant-time proofs. -/
namespace Libp2pAsm.Refinement.Identity.Certificate
open Spec.Identity.Certificate

theorem scheme_matches_iff (key scheme : Nat) : schemeMatches key scheme = true ↔
    (key = 1 ∧ scheme = 0x0807) ∨ (key = 2 ∧ scheme = 0x0403) ∨
      (key = 3 ∧ scheme = 0x0804) := by
  simp [schemeMatches, or_assoc]

theorem no_pkcs1_cv (key : Nat) : schemeMatches key 0x0401 = false := by
  simp [schemeMatches]

theorem rsa_cv_requires_pss (scheme : Nat) : schemeMatches 3 scheme = true ↔ scheme = 0x0804 := by
  simp [schemeMatches]

theorem ed_cv_rejects_ec : schemeMatches 1 0x0403 = false := rfl
theorem ec_cv_rejects_ed : schemeMatches 2 0x0807 = false := rfl

theorem host_prefix_length : hostPrefix.length = 21 := rfl
theorem server_context_length : (roleContext 1).length = 33 := rfl
theorem client_context_length : (roleContext 2).length = 33 := rfl

theorem server_message (digest : List UInt8) (h : digest.length = 32) :
    cvMessage 1 digest = .ok (List.replicate 64 32 ++ roleContext 1 ++ [0] ++ digest) := by
  simp [cvMessage, h, pure, Except.pure]

theorem client_message (digest : List UInt8) (h : digest.length = 32) :
    cvMessage 2 digest = .ok (List.replicate 64 32 ++ roleContext 2 ++ [0] ++ digest) := by
  simp [cvMessage, h, pure, Except.pure]

theorem context_message_length (role : Nat) (digest : List UInt8)
    (hr : role = 1 ∨ role = 2) (hd : digest.length = 32) :
    (cvMessage role digest).map List.length = .ok 130 := by
  rcases hr with rfl | rfl <;> simp [cvMessage, hd, roleContext, pure, Except.pure, Except.map] <;> rfl

theorem transcript_injective (role : Nat) (a b : List UInt8)
    (ha : a.length = 32) (hb : b.length = 32) (hr : role = 1 ∨ role = 2) :
    cvMessage role a = cvMessage role b ↔ a = b := by
  rcases hr with rfl | rfl <;> simp [cvMessage, ha, hb, pure, Except.pure]

theorem role_separation (a b : List UInt8) (ha : a.length = 32) (hb : b.length = 32) :
    cvMessage 1 a ≠ cvMessage 2 b := by
  rw [server_message a ha, client_message b hb]
  intro h
  have h := congrArg (fun e : Except Error (List UInt8) => e.toOption.map (fun xs => xs[73]?)) h
  change some (some (115 : UInt8)) = some (some 99) at h
  cases h

theorem valid_time_bounds (lo hi now : Int)
    (h : Spec.Identity.Time.validity lo hi now = .ok ()) :
    lo ≤ hi ∧ lo*1000000000 ≤ now ∧ now ≤ hi*1000000000 := by
  by_cases h₁ : hi < lo
  · simp [Spec.Identity.Time.validity, h₁, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  by_cases h₂ : now < lo*1000000000
  · simp [Spec.Identity.Time.validity, h₁, h₂, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  by_cases h₃ : hi*1000000000 < now
  · simp [Spec.Identity.Time.validity, h₁, h₂, h₃, throw, throwThe, MonadExceptOf.throw] at h
  omega

theorem fraction_after_expiry (lo hi delta : Int) (hdelta : 0 < delta) :
    Spec.Identity.Time.validity lo hi (hi*1000000000+delta) ≠ .ok () := by
  intro h
  have hb := valid_time_bounds lo hi _ h
  omega

theorem canonical_peer_uses_key (kind : Nat) (key : List UInt8)
    (hk : kind = 1 ∨ kind = 2) (hl : key.length = 31+kind) :
    Spec.Identity.PublicKey.peerId kind key =
      .ok ([0, (key.length+4).toUInt8, 8, kind.toUInt8, 18, key.length.toUInt8] ++ key) := by
  rcases hk with rfl | rfl <;> simp [Spec.Identity.PublicKey.peerId,
    Spec.Identity.PublicKey.encode, hl, pure, Except.pure, bind, Except.bind]

theorem canonical_peer_nonempty (kind : Nat) (key id : List UInt8)
    (h : Spec.Identity.PublicKey.peerId kind key = .ok id) : id ≠ [] := by
  unfold Spec.Identity.PublicKey.peerId at h
  cases he : Spec.Identity.PublicKey.encode kind key <;>
    simp [he, Functor.map, Except.map] at h
  subst id
  simp

theorem grammar_preserves_exact_tbs (raw : List UInt8) (span : Spec.Identity.X509.Span) :
    span.bytes raw = (raw.drop span.offset).take span.length := rfl

end Libp2pAsm.Refinement.Identity.Certificate
