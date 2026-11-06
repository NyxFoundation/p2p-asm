import Libp2pAsm.Spec.Crypto.HMAC

/-!
HKDF-SHA256, independently transcribed from RFC 5869 sections 2.2 and 2.3.
https://www.rfc-editor.org/rfc/rfc5869.html#section-2
Only SHA-256 is provided; this is not the TLS HKDF-Expand-Label encoding.
-/

namespace Libp2pAsm.Spec.Crypto.HKDF

/-- RFC 5869 section 2.2. `none` means the default 32 zero bytes;
`some []` is an explicitly empty salt (with the same HMAC result).
-/
def extract (salt : Option (List UInt8)) (ikm : List UInt8) : Except Error (List UInt8) :=
  HMAC.sha256 (salt.getD (List.replicate 32 0)) ikm

private def expandStep (prk info : Bytes) (state : Bytes × List Bytes)
    (index : Nat) : Except Error (Bytes × List Bytes) := do
  let next ← HMAC.sha256 prk (state.1 ++ info ++ [(index + 1).toUInt8])
  return (next, next :: state.2)

/-- RFC 5869 section 2.3. Require a PRK of at least 32 bytes and L <= 8160.
For valid PRKs, L=0 returns [] without computing a block. The bound is checked
before converting counters to bytes, so counters range from 1 through 255.
Longer PRKs are accepted as the RFC specifies "at least HashLen octets".
-/
def expand (prk info : List UInt8) (length : Nat) : Except Error (List UInt8) := do
  if length > 255 * 32 then throw .outputTooLong
  if prk.length < 32 then throw .prkTooShort
  let blocks := (length + 31) / 32
  let (_, reversed) ← (List.range blocks).foldlM (expandStep prk info) ([], [])
  return (reversed.reverse.flatten).take length

/-- Extract followed by expand, with the same length limit and error results. -/
def derive (salt : Option (List UInt8)) (ikm info : List UInt8)
    (length : Nat) : Except Error (List UInt8) := do
  if length > 255 * 32 then throw .outputTooLong
  let prk ← extract salt ikm
  expand prk info length

end Libp2pAsm.Spec.Crypto.HKDF
