import Libp2pAsm.Spec.Codec.Der

namespace Libp2pAsm.Spec.Identity.X509

inductive Error where
  | truncated | malformed | algorithm | duplicate | critical | missingIdentity
  deriving BEq, DecidableEq, Repr

def Error.code : Error → Nat
  | .truncated => 1 | .malformed => 6 | .algorithm => 8
  | .duplicate => 9 | .critical => 10 | .missingIdentity => 11

structure Span where
  offset : Nat
  length : Nat
  deriving BEq, DecidableEq, Repr

def Span.bytes (s : Span) (input : List UInt8) : List UInt8 :=
  input.drop s.offset |>.take s.length

structure Node where
  tag : Nat
  raw : Span
  content : Span
  deriving BEq, DecidableEq, Repr

structure Cursor where
  offset : Nat
  stop : Nat
  deriving BEq, DecidableEq, Repr

def Node.children (n : Node) : Cursor := ⟨n.content.offset, n.content.offset+n.content.length⟩

def next (input : List UInt8) (cursor : Cursor) : Except Error (Node × Cursor) := do
  if cursor.offset > cursor.stop || cursor.stop > input.length then throw .malformed
  let d ← Codec.Der.decode (input.drop cursor.offset |>.take (cursor.stop-cursor.offset))
    |>.mapError (fun e => if e == .truncated then .truncated else .malformed)
  return (⟨d.tag.toNat, ⟨cursor.offset, d.consumed⟩,
    ⟨cursor.offset+d.header, d.length⟩⟩, ⟨cursor.offset+d.consumed, cursor.stop⟩)

def expect (input : List UInt8) (cursor : Cursor) (tag : Nat) :
    Except Error (Node × Cursor) := do
  let (node, rest) ← next input cursor
  if node.tag != tag then throw .malformed
  return (node, rest)

def finished (cursor : Cursor) : Except Error Unit :=
  if cursor.offset == cursor.stop then .ok () else .error .malformed

def whole (input : List UInt8) (tag : Nat) : Except Error Node := do
  let (node, rest) ← expect input ⟨0, input.length⟩ tag
  finished rest
  return node

/-- Minimal base128 subidentifiers, including the combined first two arcs.
The value of an arc is not silently truncated into a machine integer. -/
def validOid (input : List UInt8) : Bool :=
  if input.isEmpty then false else
  let result := input.foldl (fun (state : Bool × Bool) b =>
    (state.1 && !(state.2 && b == 128), b.toNat < 128)) (true, true)
  result.1 && result.2

def oid (input : List UInt8) (cursor : Cursor) :
    Except Error (List UInt8 × Cursor) := do
  let (node, rest) ← expect input cursor 6
  let bytes := node.content.bytes input
  if !validOid bytes then throw .malformed
  return (bytes, rest)

def nullOrAbsent (input : List UInt8) (cursor : Cursor) : Except Error Unit := do
  if cursor.offset == cursor.stop then return
  let (n, rest) ← expect input cursor 5
  if n.content.length != 0 then throw .malformed
  finished rest

/-- Minimal nonnegative DER INTEGER, returning an unsigned source view.
Zero is syntactically legal; key/serial policy is a separate check. -/
def unsignedInteger (input : List UInt8) (node : Node) : Except Error Span := do
  if node.tag != 2 then throw .malformed
  let bytes := node.content.bytes input
  match bytes with
  | [] => throw .malformed
  | first :: rest =>
    if first.toNat ≥ 128 then throw .malformed
    if first != 0 || rest.isEmpty then return node.content
    if rest.head!.toNat < 128 then throw .malformed
    return ⟨node.content.offset+1, node.content.length-1⟩

def bitString (input : List UInt8) (node : Node) : Except Error Span := do
  if node.tag != 3 || node.content.length == 0 then throw .malformed
  if (node.content.bytes input).head? != some 0 then throw .malformed
  return ⟨node.content.offset+1, node.content.length-1⟩

end Libp2pAsm.Spec.Identity.X509
