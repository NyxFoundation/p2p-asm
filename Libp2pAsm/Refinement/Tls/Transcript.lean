import Libp2pAsm.Refinement.Tls.Helpers

namespace Libp2pAsm.Refinement.Tls

private theorem sha256_size (message result : List UInt8)
    (h : Spec.Crypto.SHA256.hash message = .ok result) : result.length = 32 := by
  cases hp : Spec.Crypto.SHA256.padding message.length with
  | error e => simp [Spec.Crypto.SHA256.hash, hp, bind, Except.bind] at h
  | ok suffix =>
    cases hs : Spec.Crypto.Sha2.foldBlocks 64 (by decide) Spec.Crypto.SHA256.compress
        Spec.Crypto.SHA256.initial (message ++ suffix) with
    | error e => simp [Spec.Crypto.SHA256.hash, hp, hs, bind, Except.bind] at h
    | ok state =>
      simp [Spec.Crypto.SHA256.hash, hp, hs, bind, Except.bind, pure, Except.pure] at h
      subst result
      simp [Spec.Crypto.Sha2.State.toBytes, Spec.Crypto.Sha2.encodeBE]

theorem transcript_hash_size (input result : Spec.Tls.Bytes) (limit : Nat)
    (h : Spec.Tls.Schedule.hash input limit = .ok result) : result.size = 32 := by
  unfold Spec.Tls.Schedule.hash at h
  dsimp at h
  split at h
  · change (Except.error Spec.Tls.Error.limit : Except Spec.Tls.Error _) = .ok result at h
    cases h
  · cases hs : Spec.Crypto.SHA256.hash input.toList with
    | error e => simp [hs, Except.mapError, bind, Except.bind] at h
    | ok digest =>
      simp [hs, Except.mapError, bind, Except.bind, pure, Except.pure] at h
      subst result
      simpa using sha256_size input.toList digest hs

theorem synthetic_message_size (input result : Spec.Tls.Bytes) (limit : Nat)
    (h : Spec.Tls.Schedule.messageHash input limit = .ok result) : result.size = 36 := by
  cases hh : Spec.Tls.Schedule.hash input limit with
  | error e => simp [Spec.Tls.Schedule.messageHash, hh, bind, Except.bind] at h
  | ok digest =>
    simp [Spec.Tls.Schedule.messageHash, hh, bind, Except.bind, pure, Except.pure] at h
    subst result
    have hd := transcript_hash_size input digest limit hh
    simp
    omega

end Libp2pAsm.Refinement.Tls
