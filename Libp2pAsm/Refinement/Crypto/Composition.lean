import Libp2pAsm.Asm.Crypto.Whole
import Libp2pAsm.Asm.Crypto.Link
import Libp2pAsm.Spec.Crypto.HKDF
import Libp2pAsm.Spec.Crypto.TlsKdf

/-! Universal arithmetic and pure-spec composition facts. These do not establish
instruction-level whole-function refinement, memory safety or noninterference. -/
namespace Libp2pAsm.Refinement.Crypto.Composition
open Rv64

/-- Factoring a no-return compression body leaves the wrapper instruction list intact. -/
theorem compress_body_return (v : Asm.Crypto.Sha2.Variant) :
    (Asm.Crypto.Sha2.compress v).flatten =
    (Asm.Crypto.Sha2.compressBody v).flatten ++ [.JALR .x0 .x1 0] := by
  rfl

/-- Exact split used by the SHA-512 length-field emitter, for every byte length. -/
theorem bit_length_split (n : Nat) :
    (n*8)/2^64 = n/2^61 ∧ (n*8)%2^64 = (n%2^61)*8 := by
  omega

/-- Every representable RV64 byte length fits SHA-512's 128-bit bit-length field. -/
theorem sha512_length_fits (n : Nat) (h : n < 2^64) : n*8 < 2^128 := by
  omega

/-- SHA-256's explicit byte-length rejection exactly matches the pure bit bound. -/
theorem sha256_length_iff (n : Nat) : n*8 < 2^64 ↔ n < 2^61 := by
  omega

/-- One byte suffices for every nonzero RFC 5869 block counter. -/
theorem hkdf_counter_bound (length i : Nat) (hl : length ≤ 8160)
    (hi : i < (length+31)/32) : 1 ≤ i+1 ∧ i+1 ≤ 255 := by
  omega

/-- No overflow in either checked HMAC workspace addition. -/
theorem hmac_workspace_fits (n : Nat) (h : n < 2^61-64) :
    n+64 < 2^61 ∧ max 896 (864+n) < 2^64 := by
  omega

/-- RFC 8446 requires a nonempty application label; context may be empty. -/
theorem tls_lengths (l c : Nat) (hn : 1 ≤ l) (hl : l ≤ 249) (hc : c ≤ 255) :
    7 ≤ 6+l ∧ 6+l ≤ 255 ∧ 10+l+c ≤ 514 := by
  omega

theorem tls_empty_label (length : Nat) (context : List UInt8) (h : length ≤ 65535) :
    Spec.Crypto.TlsKdf.encodeLabel length [] context = .error .labelTooShort := by
  simp [Spec.Crypto.TlsKdf.encodeLabel, Nat.not_lt.mpr h]
  rfl

theorem tls_empty_context :
    Spec.Crypto.TlsKdf.encodeLabel 0 [0x78] [] =
      .ok [0, 0, 7, 0x74, 0x6c, 0x73, 0x31, 0x33, 0x20, 0x78, 0] := by
  rfl

theorem hmac_normalized_equal (k₁ k₂ message : List UInt8)
    (h : Spec.Crypto.HMAC.normalizeKey k₁ = Spec.Crypto.HMAC.normalizeKey k₂) :
    Spec.Crypto.HMAC.sha256 k₁ message = Spec.Crypto.HMAC.sha256 k₂ message := by
  unfold Spec.Crypto.HMAC.sha256
  rw [h]

theorem zero_salt_normalize :
    Spec.Crypto.HMAC.normalizeKey (List.replicate 32 0) =
      Spec.Crypto.HMAC.normalizeKey [] := by
  simp [Spec.Crypto.HMAC.normalizeKey]

/-- The salt-length-zero ABI faithfully represents both none and some []. -/
theorem extract_default_empty (message : List UInt8) :
    Spec.Crypto.HKDF.extract none message = Spec.Crypto.HKDF.extract (some []) message := by
  exact hmac_normalized_equal (List.replicate 32 0) [] message zero_salt_normalize

end Libp2pAsm.Refinement.Crypto.Composition
