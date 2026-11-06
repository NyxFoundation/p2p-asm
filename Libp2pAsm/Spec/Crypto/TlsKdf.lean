import Libp2pAsm.Spec.Crypto.Basic

/-! RFC 8446 section 7.1 HkdfLabel encoding only (no HKDF execution).
https://www.rfc-editor.org/rfc/rfc8446.html#section-7.1
The fixed ASCII prefix has six bytes. Label/context are exact opaque bytes;
there is no extra policy restricting their contents. -/
namespace Libp2pAsm.Spec.Crypto.TlsKdf

inductive Error where
  | outputTooLong | labelTooShort | labelTooLong | contextTooLong
  deriving DecidableEq, BEq, Repr

/-- Output length is a uint16, prefixed label length is 7..255, context 0..255.
This encoder's uint16 domain is distinct from HKDF-SHA256's 8160-byte limit. -/
def encodeLabel (length : Nat) (label context : Bytes) : Except Error Bytes := do
  if length > 65535 then throw .outputTooLong
  if label.isEmpty then throw .labelTooShort
  if label.length > 249 then throw .labelTooLong
  if context.length > 255 then throw .contextTooLong
  return Sha2.encodeBE 2 length ++ [(6+label.length).toUInt8] ++
    [0x74, 0x6c, 0x73, 0x31, 0x33, 0x20] ++ label ++
    [context.length.toUInt8] ++ context

end Libp2pAsm.Spec.Crypto.TlsKdf
