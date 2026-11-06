import Libp2pAsm.Refinement.Identity.View

namespace Libp2pAsm.Refinement.Identity
open Spec.Identity.PublicKey

/-- Identity multihash over the deterministic Type/Data encoding, for arbitrary raw key bytes. -/
theorem canonical_peerId (kind : Nat) (key : List UInt8) (hk : kind=1 ∨ kind=2)
    (hl : key.length=31+kind) :
    peerId kind key = .ok ([0,(35+kind).toUInt8,8,kind.toUInt8,18,(31+kind).toUInt8]++key) := by
  rcases hk with rfl | rfl <;>
    simp [peerId,encode,hl,bind,Except.bind,pure,Except.pure]

theorem canonical_size (kind : Nat) (key : List UInt8) (hk : kind=1 ∨ kind=2)
    (hl : key.length=31+kind) :
    ([0,(35+kind).toUInt8,8,kind.toUInt8,18,(31+kind).toUInt8]++key).length=37+kind ∧
      (37+kind=38 ∨ 37+kind=39) ∧ 35+kind ≤ 42 := by
  simp only [List.length_append,List.length_cons,List.length_nil,hl]
  omega

theorem rejects_raw_enum (kind : Nat) (key : List UInt8) (hk : kind≠1 ∧ kind≠2) :
    peerId kind key = .error .keyType := by
  simp [peerId,encode,hk.1,hk.2,bind,Except.bind,throw,throwThe,MonadExceptOf.throw]

theorem rejects_key_length (kind : Nat) (key : List UInt8) (hk : kind=1 ∨ kind=2)
    (hl : key.length ≠ 31+kind) : peerId kind key = .error .keyLength := by
  rcases hk with rfl | rfl <;>
    simp [peerId,encode,hl,bind,Except.bind,throw,throwThe,MonadExceptOf.throw]

end Libp2pAsm.Refinement.Identity
