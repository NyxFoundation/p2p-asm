import Libp2pAsm.Refinement.Identity.PeerRaw

namespace Libp2pAsm.Refinement.Identity.Peer
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmProtobuf.Footprint

theorem rawWrites_bounds (kind key length out cap : Word) (a : Nat × Word)
    (h : a∈rawWrites kind key length out cap) :
    a.1=1 ∧ out.toNat≤a.2.toNat ∧ a.2.toNat+1≤out.toNat+(length.toNat+6) := by
  unfold rawWrites at h
  cases he : rawError kind key length out cap with
  | some e => simp [he] at h
  | none =>
    simp only [he] at h
    exact byteReads_bounds out _ _ (Nat.le_refl _) (validated _ _ _ _ _ he).2.2.2.2.2.1 a h

theorem rawReads_bounds (kind key length out cap : Word) (a : Nat × Word)
    (h : a∈rawReads kind key length out cap) :
    a.1=1 ∧ key.toNat≤a.2.toNat ∧ a.2.toNat+1≤key.toNat+length.toNat := by
  unfold rawReads at h
  cases he : rawError kind key length out cap with
  | some e => simp [he] at h
  | none =>
    simp only [he] at h
    exact byteReads_bounds key _ _ (Nat.le_refl _) (validated _ _ _ _ _ he).2.2.2.2.1 a h

/-- The output is regenerated from key bytes, independent of any received protobuf representation. -/
theorem result_spec (kind key length out cap : Word) (data encoded : List UInt8)
    (hl : length.toNat=data.length) (h : result kind key length out cap data=.ok encoded) :
    Spec.Identity.PublicKey.peerId kind.toNat data=.ok encoded ∧ (encoded.length=38 ∨ encoded.length=39) := by
  unfold result at h
  cases he : rawError kind key length out cap with
  | some e => simp [he] at h
  | none =>
    simp only [he,Except.ok.injEq] at h
    subst encoded
    have hv := validated _ _ _ _ _ he
    exact ⟨canonical_spec kind data hv.1 (by omega),by rw [canonical_length]; omega⟩

end Libp2pAsm.Refinement.Identity.Peer
