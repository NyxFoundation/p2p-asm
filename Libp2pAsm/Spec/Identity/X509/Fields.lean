import Libp2pAsm.Spec.Identity.X509.Algorithm
import Libp2pAsm.Spec.Identity.Time

namespace Libp2pAsm.Spec.Identity.X509

def foldNodes (input : List UInt8) (step : α → Node → Except Error α) :
    Nat → Cursor → α → Except Error α
  | 0, cursor, acc => if cursor.offset == cursor.stop then .ok acc else .error .malformed
  | fuel+1, cursor, acc => do
    if cursor.offset == cursor.stop then return acc
    let (node, rest) ← next input cursor
    let acc ← step acc node
    foldNodes input step fuel rest acc

def boolean (input : List UInt8) (node : Node) : Except Error Bool := do
  if node.tag != 1 then throw .malformed
  match node.content.bytes input with
  | [0] => return false
  | [255] => return true
  | _ => throw .malformed

private def printable (b : UInt8) : Bool :=
  let n := b.toNat
  (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) || (48 ≤ n && n ≤ 57) ||
    [32, 39, 40, 41, 43, 44, 45, 46, 47, 58, 61, 63].contains n

private def unicodeScalar (n : Nat) : Bool :=
  n ≤ 0x10ffff && !(0xd800 ≤ n && n ≤ 0xdfff)

private def wideString (width : Nat) (bytes : List UInt8) : Bool :=
  bytes.length % width == 0 && (List.range (bytes.length/width)).all fun i =>
    unicodeScalar ((bytes.drop (i*width) |>.take width).foldl (fun n b => 256*n+b.toNat) 0)

/-- Validate common directory-string encodings, while keeping unknown attribute
types opaque. Names are not DNS names or a substitute for libp2p identity. -/
private def validateAttribute (bytes : List UInt8) (node : Node) : Except Error Unit := do
  if node.tag != 48 then throw .malformed
  let (_, cursor) ← oid bytes node.children
  let (value, done) ← next bytes cursor
  finished done
  let content := value.content.bytes bytes
  let valid := match value.tag with
    | 12 => (String.fromUTF8? ⟨content.toArray⟩).isSome
    | 18 => content.all fun b => b == 32 || (48 ≤ b.toNat && b.toNat ≤ 57)
    | 19 => content.all printable
    | 22 => content.all fun b => b.toNat < 128
    | 28 => wideString 4 content
    | 30 => wideString 2 content
    | _ => true
  if !valid then throw .malformed

private def nameSet (bytes : List UInt8) (_ : Unit) (node : Node) : Except Error Unit := do
  if node.tag != 49 || node.content.length == 0 then throw .malformed
  let _ ← foldNodes bytes (fun (previous : Option (List UInt8)) attr => do
    validateAttribute bytes attr
    let encoded := attr.raw.bytes bytes
    if let some prev := previous then
      if compare prev encoded == .gt then throw .malformed
    return some encoded) node.content.length node.children none

def name (bytes : List UInt8) (node : Node) : Except Error Unit := do
  if node.tag != 48 then throw .malformed
  foldNodes bytes (nameSet bytes) node.content.length node.children ()

structure PublicKeyView where
  kind : Nat
  data : Span
  modulus : Span := ⟨0, 0⟩
  exponent : Span := ⟨0, 0⟩
  deriving BEq, DecidableEq, Repr

private def rsaKey (bytes : List UInt8) (data : Span) : Except Error PublicKeyView := do
  let (seq, done) ← expect bytes ⟨data.offset, data.offset+data.length⟩ 48
  finished done
  let (modulus, cursor) ← expect bytes seq.children 2
  let (exponent, done) ← expect bytes cursor 2
  finished done
  return ⟨3, data, ← unsignedInteger bytes modulus, ← unsignedInteger bytes exponent⟩

def publicKey (bytes : List UInt8) (node : Node) : Except Error PublicKeyView := do
  if node.tag != 48 then throw .malformed
  let (algorithm, cursor) ← expect bytes node.children 48
  let kind ← publicKeyAlgorithm (algorithm.raw.bytes bytes) |>.mapError (fun _ => .algorithm)
  let (bits, done) ← expect bytes cursor 3
  finished done
  let data ← bitString bytes bits
  if kind == 3 then return ← rsaKey bytes data
  if kind == 1 then
    if data.length != 32 then throw .malformed
  else if data.length != 65 || (data.bytes bytes).head? != some 4 then throw .malformed
  return ⟨kind, data, ⟨0, 0⟩, ⟨0, 0⟩⟩

def validity (bytes : List UInt8) (node : Node) : Except Error (Int × Int) := do
  if node.tag != 48 then throw .malformed
  let (before, cursor) ← next bytes node.children
  let (after, done) ← next bytes cursor
  finished done
  let first ← Time.decode before.tag (before.content.bytes bytes) |>.mapError (fun _ => .malformed)
  let last ← Time.decode after.tag (after.content.bytes bytes) |>.mapError (fun _ => .malformed)
  if last < first then throw .malformed
  return (first, last)

end Libp2pAsm.Spec.Identity.X509
