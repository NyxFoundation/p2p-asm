import Libp2pAsm.Spec.Codec.QuicVarint
import Libp2pAsm.Spec.Codec.UnsignedVarint

namespace Libp2pAsm.Tests.Codec

open Spec.Codec

private def check (name : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"FAIL: {name}")

private def roundTrip (encode : Nat → Except Error (List UInt8))
    (decode : List UInt8 → Except Error Decoded) (value : Nat) : IO Unit := do
  let .ok bytes := encode value | throw (IO.userError "Encoder rejected a valid value.")
  check "should recover the value and consume only its encoded prefix"
    (match decode (bytes ++ [0xaa, 0xbb]) with
      | .ok d => d.value == value && d.consumed == bytes.length
      | _ => false)
  for n in List.range bytes.length do
    check "should reject each truncated prefix"
      (match decode (bytes.take n) with | .error .truncated => true | _ => false)

private def quic : IO Unit := do
  for (bytes, value) in [
      ([0x25], 37), ([0x7b, 0xbd], 15293), ([0x9d, 0x7f, 0x3e, 0x7d], 494878333),
      ([0xc2, 0x19, 0x7c, 0x5e, 0xff, 0x14, 0xe8, 0x8c], 151288809941952652)] do
    check "should decode the RFC 9000 vector"
      (match QuicVarint.decode bytes with | .ok d => d.value == value | _ => false)
    check "should encode the RFC 9000 vector"
      (match QuicVarint.encode value with | .ok actual => actual == bytes | _ => false)
  for value in List.range 1024 ++ [16383, 16384, 2^30-1, 2^30, 2^62-1] do
    roundTrip QuicVarint.encode QuicVarint.decode value
  check "should allow non-minimal QUIC encodings"
    (match QuicVarint.decode [0x40, 0] with
      | .ok d => d.value == 0 && d.consumed == 2 | _ => false)
  check "should reject QUIC values at or above 2^62"
    (match QuicVarint.encode (2^62) with | .error .overflow => true | _ => false)

private def unsigned : IO Unit := do
  for value in List.range 1024 ++ [16383, 16384, 2^28-1, 2^56, 2^63-1] do
    roundTrip UnsignedVarint.encode UnsignedVarint.decode value
  for bytes in [[0x80, 0], [0x81, 0], [0x80, 0x80, 0]] do
    check "should reject non-minimal multiformats varints"
      (match UnsignedVarint.decode bytes with | .error .nonMinimal => true | _ => false)
  check "should reject continuation in the ninth unsigned-varint byte"
    (match UnsignedVarint.decode (List.replicate 9 0x80) with
      | .error .overflow => true | _ => false)
  check "should reject unsigned-varint values at or above 2^63"
    (match UnsignedVarint.encode (2^63) with | .error .overflow => true | _ => false)

def run : IO Unit := do
  quic
  unsigned
  IO.println "PASS: should encode/decode QUIC and multiformats varints across vectors, boundaries and truncation"

end Libp2pAsm.Tests.Codec
