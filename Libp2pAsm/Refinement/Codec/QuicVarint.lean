import Libp2pAsm.Refinement.Codec.QuicHelpers

namespace Libp2pAsm.Refinement.Codec.QuicVarint

open Spec.Codec Spec.Codec.QuicVarint

theorem encode_length (value : Nat) (h : value < 2^62) :
    ∃ bytes, encode value = .ok bytes ∧ bytes.length = (widthTag value).1 := by
  simp only [encode, show ¬value ≥ 2^62 by omega, ↓reduceIte]
  refine ⟨_, rfl, ?_⟩
  have hw : 0 < (widthTag value).1 := by
    unfold widthTag
    split <;> (try split) <;> (try split) <;> simp
  simp only [List.length_cons, bigEndian_length]
  omega

/-- The full 62-bit domain round-trips, consuming exactly the encoded width. -/
theorem roundTrip (value : Nat) (h : value < 2^62) (suffix : List UInt8) :
    ∃ bytes, encode value = .ok bytes ∧
      decode (bytes ++ suffix) = .ok ⟨value, (widthTag value).1⟩ ∧
      bytes.length = (widthTag value).1 := by
  obtain ⟨bytes, he, hl⟩ := encode_length value h
  refine ⟨bytes, he, ?_, hl⟩
  clear hl
  simp only [encode, show ¬value ≥ 2^62 by omega, ↓reduceIte] at he
  cases hw : widthTag value with
  | mk width tag =>
    simp only [hw, Except.ok.injEq] at he
    subst bytes
    unfold widthTag at hw
    split at hw <;> (try split at hw) <;> (try split at hw) <;>
      simp only [Prod.mk.injEq] at hw
    all_goals obtain ⟨rfl, rfl⟩ := hw
    · exact decode_fixedWidth 0 value suffix (by decide) (by simpa using ‹value < 2^6›)
    · exact decode_fixedWidth 1 value suffix (by decide) (by simpa using ‹value < 2^14›)
    · exact decode_fixedWidth 2 value suffix (by decide) (by simpa using ‹value < 2^30›)
    · exact decode_fixedWidth 3 value suffix (by decide) h

theorem decode_bounds (input : List UInt8) (d : Decoded) (hd : decode input = .ok d) :
    1 ≤ d.consumed ∧ d.consumed ≤ 8 ∧ d.consumed ≤ input.length ∧ d.value < 2^62 := by
  cases input with
  | nil => simp [decode] at hd
  | cons first rest =>
    simp only [decode_cons] at hd
    split at hd
    · cases hd
    · rename_i hn
      cases hd
      have hb := first.toNat_lt
      have hf := fold_value_bound (rest.take (2^(first.toNat / 64) - 1))
        (first.toNat % 64) 64 (by omega)
      have hl : (rest.take (2^(first.toNat / 64) - 1)).length =
          2^(first.toNat / 64) - 1 := by simp; omega
      rw [hl] at hf
      have ht : first.toNat / 64 = 0 ∨ first.toNat / 64 = 1 ∨
          first.toNat / 64 = 2 ∨ first.toNat / 64 = 3 := by omega
      rcases ht with ht | ht | ht | ht <;>
        simp only [ht, Nat.reducePow, Nat.reduceSub, List.length_cons] at hf hn ⊢ <;> omega

theorem decode_consumed (first : UInt8) (rest : List UInt8) (d : Decoded)
    (hd : decode (first :: rest) = .ok d) : d.consumed = 2^(first.toNat / 64) := by
  simp only [decode_cons] at hd
  split at hd
  · cases hd
  · cases hd; rfl

theorem decode_truncated_iff (first : UInt8) (rest : List UInt8) :
    decode (first :: rest) = .error .truncated ↔ rest.length < 2^(first.toNat / 64) - 1 := by
  simp only [decode_cons]
  split <;> simp_all

/-- Every proper prefix of an encoded QUIC value is truncated. -/
theorem decode_truncated (value : Nat) (bytes : List UInt8) (he : encode value = .ok bytes)
    (n : Nat) (hn : n < bytes.length) : decode (bytes.take n) = .error .truncated := by
  have hv : value < 2^62 := by
    by_cases hv : value < 2^62
    · exact hv
    · simp [encode, show value ≥ 2^62 by omega] at he
  obtain ⟨encoded, he', hd, hl⟩ := roundTrip value hv []
  have hb : encoded = bytes := by rw [he] at he'; cases he'; rfl
  subst encoded
  simp only [List.append_nil] at hd
  cases bytes with
  | nil => simp at hn
  | cons first rest =>
    have hw := decode_consumed first rest _ hd
    simp only at hw
    cases n with
    | zero => rfl
    | succ n =>
      apply (decode_truncated_iff first (rest.take n)).2
      simp only [List.length_take]
      simp only [List.length_cons] at hn hl
      omega

theorem header_width (first : UInt8) :
    2^(first.toNat / 64) = 1 ∨ 2^(first.toNat / 64) = 2 ∨
      2^(first.toNat / 64) = 4 ∨ 2^(first.toNat / 64) = 8 := by
  have hb := first.toNat_lt
  have ht : first.toNat / 64 = 0 ∨ first.toNat / 64 = 1 ∨
      first.toNat / 64 = 2 ∨ first.toNat / 64 = 3 := by omega
  rcases ht with ht | ht | ht | ht <;> simp only [ht] <;> decide

theorem decode_width (input : List UInt8) (d : Decoded) (hd : decode input = .ok d) :
    d.consumed = 1 ∨ d.consumed = 2 ∨ d.consumed = 4 ∨ d.consumed = 8 := by
  cases input with
  | nil => simp [decode] at hd
  | cons first rest => rw [decode_consumed first rest d hd]; exact header_width first

/-- Even malformed input has no dependency on bytes after the eighth. -/
theorem decode_bounded (input : List UInt8) : decode (input.take 8) = decode input := by
  cases input with
  | nil => rfl
  | cons first rest =>
    have hw : 2^(first.toNat / 64) - 1 ≤ 7 := by
      have := header_width first
      omega
    have hg : (min 7 rest.length < 2^(first.toNat / 64) - 1) ↔
        rest.length < 2^(first.toNat / 64) - 1 := by omega
    simp only [List.take_succ_cons, decode_cons, List.length_take, hg, List.take_take,
      Nat.min_eq_left hw]

theorem encode_width (value : Nat) (bytes : List UInt8) (he : encode value = .ok bytes) :
    bytes.length = (widthTag value).1 ∧ value < 2^62 := by
  have hv : value < 2^62 := by
    by_cases hv : value < 2^62
    · exact hv
    · simp [encode, show value ≥ 2^62 by omega] at he
  obtain ⟨encoded, he', hl⟩ := encode_length value hv
  rw [he] at he'
  cases he'
  exact ⟨hl, hv⟩

end Libp2pAsm.Refinement.Codec.QuicVarint
