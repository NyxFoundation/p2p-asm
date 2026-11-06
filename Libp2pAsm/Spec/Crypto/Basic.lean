import Std

/-!
Pure, byte-oriented reference specifications. These definitions are intended for
tests and refinement statements, not as the production cryptographic runtime.
No constant-time, zeroization, or cryptographic-security claim is made here.
-/

namespace Libp2pAsm.Spec.Crypto

abbrev Bytes := List UInt8

inductive Error where
  | messageTooLong
  | invalidBlockLength
  | outputTooLong
  | prkTooShort
  deriving DecidableEq, BEq, Repr

namespace Sha2

/-- Eight working words, in the order used in FIPS 180-4 sections 6.2 and 6.4. -/
structure State (width : Nat) where
  a : BitVec width
  b : BitVec width
  c : BitVec width
  d : BitVec width
  e : BitVec width
  f : BitVec width
  g : BitVec width
  h : BitVec width
  deriving DecidableEq, BEq, Repr

def State.add (x y : State w) : State w :=
  ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d,
   x.e + y.e, x.f + y.f, x.g + y.g, x.h + y.h⟩

def choose (x y z : BitVec w) : BitVec w :=
  (x &&& y) ^^^ (~~~x &&& z)

def majority (x y z : BitVec w) : BitVec w :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Big-endian low `count` bytes. Callers check length-field bounds before use. -/
def encodeBE (count value : Nat) : Bytes :=
  (List.range count).map fun i => (value / 2^(8 * (count - 1 - i)) % 256).toUInt8

def readWord (width : Nat) (bytes : Bytes) : BitVec width :=
  bytes.foldl (fun word byte => (word <<< 8) ||| BitVec.ofNat width byte.toNat) 0

def State.toBytes (s : State w) : Bytes :=
  [s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h].flatMap (fun x => encodeBE (w / 8) x.toNat)

/-- FIPS 180-4 section 5.1, for byte-aligned input; all arithmetic is in `Nat`.
`blockBytes` and `lengthBytes` are fixed to (64,8) or (128,16) by the callers.
The returned suffix includes 0x80, zeros, and the full big-endian bit length.
https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf -/
def padding (blockBytes lengthBytes byteLength : Nat) : Except Error Bytes := do
  if byteLength * 8 ≥ 2^(8 * lengthBytes) then throw .messageTooLong
  let zeroCount := (blockBytes - (byteLength + 1 + lengthBytes) % blockBytes) % blockBytes
  return [0x80] ++ List.replicate zeroCount 0 ++ encodeBE lengthBytes (byteLength * 8)

/-- Consume complete blocks. A partial block is an explicit error, never zero-filled.
Recursion decreases the input length; compression receives a fixed-size vector.
-/
def foldBlocks {α : Type} (size : Nat) (positive : 0 < size)
    (compress : α → Vector UInt8 size → α) (state : α)
    (bytes : Bytes) : Except Error α :=
  if bytes.isEmpty then .ok state
  else
    let chunk := (bytes.take size).toArray
    if enough : chunk.size = size then
      foldBlocks size positive compress (compress state ⟨chunk, enough⟩) (bytes.drop size)
    else .error .invalidBlockLength
termination_by bytes.length
decreasing_by simp_all [chunk]; omega

end Sha2
end Libp2pAsm.Spec.Crypto
