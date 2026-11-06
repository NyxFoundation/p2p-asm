import Libp2pAsm.Spec.Identity.X509.Fields

namespace Libp2pAsm.Spec.Identity.X509

def libp2pOid : List UInt8 := [43, 6, 1, 4, 1, 131, 162, 90, 1, 1]

structure Extensions where
  ids : List (List UInt8) := []
  identity : Option (Span × Span) := none
  keyUsage : Bool := true
  extendedUsage : Nat := 3
  deriving Repr

private def signedKey (bytes : List UInt8) (value : Node) : Except Error (Span × Span) := do
  let (seq, done) ← expect bytes value.children 48
  finished done
  let (key, cursor) ← expect bytes seq.children 4
  let (signature, done) ← expect bytes cursor 4
  finished done
  return (key.content, signature.content)

private def keyUsage (bytes : List UInt8) (value : Node) : Except Error Bool := do
  let (bits, done) ← expect bytes value.children 3
  finished done
  match bits.content.bytes bytes with
  | unused :: data =>
    if unused.toNat > 7 || data.length > 2 then throw .malformed
    if data.isEmpty then
      if unused != 0 then throw .malformed
      return false
    let last := data.getLast!
    if last.toNat % (2^unused.toNat) != 0 then throw .malformed
    if last == 0 || last.toNat / (2^unused.toNat) % 2 != 1 then throw .malformed
    if data.length == 2 && (unused != 7 || last != 128) then throw .malformed
    return data.head!.toNat ≥ 128
  | [] => throw .malformed

private def basicConstraints (bytes : List UInt8) (value : Node) : Except Error Unit := do
  let (seq, done) ← expect bytes value.children 48
  finished done
  let cursor := seq.children
  if cursor.offset == cursor.stop then return
  let (first, rest) ← next bytes cursor
  let (ca, cursor) ← if first.tag == 1 then do
    let ca ← boolean bytes first
    pure (ca, rest)
    else pure (false, cursor)
  if cursor.offset == cursor.stop then return
  if !ca then throw .malformed
  let (pathLen, done) ← expect bytes cursor 2
  let _ ← unsignedInteger bytes pathLen
  finished done

private def usage (bytes : List UInt8) (value : Node) : Except Error Nat := do
  let (seq, done) ← expect bytes value.children 48
  finished done
  if seq.content.length == 0 then throw .malformed
  foldNodes bytes (fun flags node => do
    if node.tag != 6 then throw .malformed
    let id := node.content.bytes bytes
    if !validOid id then throw .malformed
    if id == [85, 29, 37, 0] then return 3
    if id == [43, 6, 1, 5, 5, 7, 3, 1] then return flags ||| 1
    if id == [43, 6, 1, 5, 5, 7, 3, 2] then return flags ||| 2
    return flags) seq.content.length seq.children 0

private def process (bytes : List UInt8) (state : Extensions) (node : Node) :
    Except Error Extensions := do
  if node.tag != 48 then throw .malformed
  let (id, cursor) ← oid bytes node.children
  if state.ids.contains id then throw .duplicate
  let state := { state with ids := id :: state.ids }
  let (first, rest) ← next bytes cursor
  let (critical, value, done) ← if first.tag == 1 then do
    let critical ← boolean bytes first
    let (value, done) ← expect bytes rest 4
    pure (critical, value, done)
    else pure (false, first, rest)
  if value.tag != 4 then throw .malformed
  finished done
  if id == libp2pOid then
    return { state with identity := some (← signedKey bytes value) }
  if id == [85, 29, 15] then
    return { state with keyUsage := ← keyUsage bytes value }
  if id == [85, 29, 19] then
    basicConstraints bytes value
    return state
  if id == [85, 29, 37] then
    return { state with extendedUsage := ← usage bytes value }
  if critical then throw .critical
  return state

/-- Unknown noncritical extnValue bytes remain opaque. Known critical extensions
are understood here; unsupported critical extensions are never silently ignored. -/
def extensions (bytes : List UInt8) (node : Node) : Except Error Extensions := do
  if node.tag != 0xa3 then throw .malformed
  let (seq, done) ← expect bytes node.children 48
  finished done
  if seq.content.length == 0 then throw .missingIdentity
  let parsed ← foldNodes bytes (process bytes) seq.content.length seq.children {}
  if parsed.identity.isNone then throw .missingIdentity
  return parsed

end Libp2pAsm.Spec.Identity.X509
