import Libp2pAsm.Spec.Codec.ProtobufVarint

/-! libp2p PublicKey proto2 wire parsing and canonical inline Peer IDs.
Field order, repeated singular fields, non-minimal varints and unknown fields
(including correctly nested groups) follow protobuf semantics. Curve-point
validity and signatures are separate authentication obligations. -/
namespace Libp2pAsm.Spec.Identity.PublicKey

inductive Error where
  | truncated | overflow | range | capacity | wire | missing | keyType | keyLength
  deriving BEq, DecidableEq, Repr

def Error.code : Error → Nat
  | .truncated => 1 | .overflow => 2 | .range => 4 | .capacity => 5
  | .wire => 6 | .missing => 7 | .keyType => 8 | .keyLength => 9

structure View where
  kind : Nat
  offset : Nat
  length : Nat
  deriving BEq, DecidableEq, Repr

structure ParseState where
  rest : List UInt8
  offset : Nat := 0
  groups : List Nat := []
  kind : Option Nat := none
  data : Option (Nat × Nat) := none

def advance (s : ParseState) (count : Nat) : ParseState :=
  { s with rest := s.rest.drop count, offset := s.offset + count }

def readVarint (s : ParseState) : Except Error (Nat × ParseState) := do
  let d ← (Spec.Codec.ProtobufVarint.decode s.rest).mapError fun
    | .truncated => .truncated | _ => .overflow
  return (d.value, advance s d.consumed)

def skip (s : ParseState) (count : Nat) : Except Error ParseState :=
  if s.rest.length < count then .error .truncated else .ok (advance s count)

private def lengthField (s : ParseState) (field : Nat) : Except Error ParseState := do
  let (length, next) ← readVarint s
  let last ← skip next length
  return if s.groups.isEmpty && field == 2 then
    { last with data := some (next.offset, length) } else last

private def value (s : ParseState) (field wire : Nat) : Except Error ParseState := do
  match wire with
  | 0 =>
    let (n, next) ← readVarint s
    return if s.groups.isEmpty && field == 1 then { next with kind := some n } else next
  | 1 => skip s 8
  | 2 => lengthField s field
  | 3 => return { s with groups := field :: s.groups }
  | 4 =>
    match s.groups with
    | expected :: tail =>
      if field != expected then throw .wire
      return { s with groups := tail }
    | [] => throw .wire
  | 5 => skip s 4
  | _ => throw .wire

private def complete (s : ParseState) : Except Error View := do
  if !s.groups.isEmpty then throw .truncated
  let some kind := s.kind | throw .missing
  let some (offset, length) := s.data | throw .missing
  if kind != 1 && kind != 2 then throw .keyType
  if length != 31 + kind then throw .keyLength
  return ⟨kind, offset, length⟩

/-- Each nonempty iteration consumes at least the tag varint. -/
def parse : Nat → ParseState → Except Error View
  | 0, s => if s.rest.isEmpty then complete s else .error .overflow
  | fuel+1, s => do
    if s.rest.isEmpty then return ← complete s
    let (tag, next) ← readVarint s
    if tag / 8 == 0 || tag ≥ 2^32 then throw .wire
    parse fuel (← value next (tag / 8) (tag % 8))

def decode (bytes : List UInt8) : Except Error View :=
  if bytes.length ≥ 2^61 then .error .overflow else parse (bytes.length+1) { rest := bytes }

def encode (kind : Nat) (key : List UInt8) : Except Error (List UInt8) := do
  if kind != 1 && kind != 2 then throw .keyType
  if key.length != 31 + kind then throw .keyLength
  return [8, kind.toUInt8, 18, key.length.toUInt8] ++ key

/-- Both supported key encodings fit the mandatory <=42-byte identity-multihash rule. -/
def peerId (kind : Nat) (key : List UInt8) : Except Error (List UInt8) := do
  let encoded ← encode kind key
  return [0, encoded.length.toUInt8] ++ encoded

end Libp2pAsm.Spec.Identity.PublicKey
