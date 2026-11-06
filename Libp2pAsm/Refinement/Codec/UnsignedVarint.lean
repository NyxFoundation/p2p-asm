import Libp2pAsm.Refinement.Codec.UnsignedCanonical
import Libp2pAsm.Refinement.Codec.UnsignedErrors

namespace Libp2pAsm.Refinement.Codec.UnsignedVarint

open Spec.Codec Spec.Codec.UnsignedVarint

/-- Every value in the full 63-bit domain round-trips with an arbitrary trailing input. -/
theorem roundTrip (value : Nat) (hv : value < 2^63) (suffix : List UInt8) :
    ∃ bytes, encode value = .ok bytes ∧
      decode (bytes ++ suffix) = .ok ⟨value, bytes.length⟩ ∧
      0 < bytes.length ∧ bytes.length ≤ 9 := by
  obtain ⟨bytes, he, hp, hl⟩ := encodeLoop_exists 9 value (by decide) hv
  refine ⟨bytes, ?_, ?_, hp, hl⟩
  · simp only [encode, show ¬value ≥ 2^63 by omega, ↓reduceIte, he]
  · simpa [decode] using decodeLoop_encodeLoop 9 value bytes suffix he 0 0 0 (Or.inl rfl)

theorem encode_width (value : Nat) (bytes : List UInt8) (he : encode value = .ok bytes) :
    0 < bytes.length ∧ bytes.length ≤ 9 ∧ value < 128^bytes.length ∧
      (bytes.length = 1 ∨ 128^(bytes.length - 1) ≤ value) := by
  simp only [encode] at he
  split at he
  · cases he
  · exact encodeLoop_width _ _ _ he

/-- Exact byte width, including the one-byte encoding of zero. -/
theorem encode_width_iff (value : Nat) (bytes : List UInt8) (he : encode value = .ok bytes)
    (width : Nat) (hw : 0 < width) :
    bytes.length = width ↔ value < 128^width ∧
      (width = 1 ∨ 128^(width - 1) ≤ value) := by
  obtain ⟨hp, _, hu, hl⟩ := encode_width value bytes he
  constructor
  · intro h; simpa [h] using And.intro hu hl
  · intro ⟨hwu, hwl⟩
    exact minimal_width_unique value bytes.length width hp hw hu hwu hl hwl

theorem decode_bounds (input : List UInt8) (d : Decoded) (hd : decode input = .ok d) :
    1 ≤ d.consumed ∧ d.consumed ≤ 9 ∧ d.consumed ≤ input.length ∧ d.value < 2^63 := by
  have hc := decodeLoop_consumption 9 input 0 0 0 d hd
  have hv := decodeLoop_value_bound 9 input 0 0 0 d (by decide) hd
  simp only [Nat.zero_add] at hc hv
  exact ⟨hc.1, hc.2.1, hc.2.2, hv⟩

theorem decode_width_iff (input : List UInt8) (d : Decoded) (hd : decode input = .ok d)
    (width : Nat) (hw : 0 < width) :
    d.consumed = width ↔ d.value < 128^width ∧
      (width = 1 ∨ 128^(width - 1) ≤ d.value) := by
  have hb := decode_bounds input d hd
  obtain ⟨hu, hl⟩ := decode_width input d hd
  constructor
  · intro h; simpa [h] using And.intro hu hl
  · intro ⟨hwu, hwl⟩
    exact minimal_width_unique d.value d.consumed width hb.1 hw hu hwu hl hwl

end Libp2pAsm.Refinement.Codec.UnsignedVarint
