import Std

/-! X.690 definite/minimal TLV headers for the low-tag-number certificate profile.
This is not validation of ASN.1 value contents. Unknown non-critical extension
contents remain opaque; callers validate expected tags, INTEGERs, OIDs and times. -/
namespace Libp2pAsm.Spec.Codec.Der

inductive Error where
  | truncated | overflow | nonMinimal | range | capacity
  | unsupportedTag | indefinite | reserved
  deriving DecidableEq, BEq, Repr

def Error.code : Error → Nat
  | .truncated => 1 | .overflow => 2 | .nonMinimal => 3 | .range => 4
  | .capacity => 5 | .unsupportedTag => 6 | .indefinite => 7 | .reserved => 8

structure Decoded where
  tag : UInt8
  header : Nat
  length : Nat
  consumed : Nat
  deriving DecidableEq, BEq, Repr

/-- Reject high-tag form and universal end-of-contents, not context-specific tag 0. -/
def supportedTag (tag : Nat) : Bool :=
  tag < 256 && tag % 32 != 31 && (tag ≥ 64 || tag % 32 != 0)

/-- A length needing more than eight octets cannot fit this 64-bit ABI. -/
def decode (bytes : List UInt8) : Except Error Decoded := do
  let tag :: rest := bytes | throw .truncated
  if !supportedTag tag.toNat then throw .unsupportedTag
  let first :: tail := rest | throw .truncated
  if first.toNat < 128 then
    if tail.length < first.toNat then throw .truncated
    return ⟨tag, 2, first.toNat, 2 + first.toNat⟩
  if first == 128 then throw .indefinite
  if first == 255 then throw .reserved
  let count := first.toNat % 128
  if count > 8 then throw .overflow
  if tail.length < count then throw .truncated
  if tail.head? == some 0 then throw .nonMinimal
  let length := (tail.take count).foldl (fun acc b => 256*acc + b.toNat) 0
  if length < 128 then throw .nonMinimal
  if tail.length - count < length then throw .truncated
  return ⟨tag, 2 + count, length, 2 + count + length⟩

def significantBytes (n : Nat) : List UInt8 :=
  if _h : n = 0 then [] else significantBytes (n / 256) ++ [n.toUInt8]
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

/-- Header only; caller separately owns the payload and the entire TLV capacity. -/
def encodeHeader (tag length : Nat) : Except Error (List UInt8) := do
  if !supportedTag tag then throw .unsupportedTag
  if length ≥ 2^64 then throw .overflow
  if length < 128 then return [tag.toUInt8, length.toUInt8]
  let bytes := significantBytes length
  return [tag.toUInt8, (128 + bytes.length).toUInt8] ++ bytes

end Libp2pAsm.Spec.Codec.Der
