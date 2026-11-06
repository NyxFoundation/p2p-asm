import Libp2pAsm.Spec.Tls.View

namespace Libp2pAsm.Spec.Tls

structure Extension where
  kind : Nat
  data : Slice
  deriving Repr

/-- At most floor(bytes/4) extension headers; duplicate even unknown IDs fail. -/
def extensions (c : Cursor) : Except Error (Array Extension) := do
  let mut current := c
  let mut seen : List Nat := []
  let mut result := #[]
  for _ in List.range ((c.stop-c.pos)/4) do
    if current.pos == current.stop then break
    let (kind,next) ← current.uint 2
    let (data,next) ← next.vector 2 0
    if seen.contains kind then throw .duplicate
    seen := kind :: seen
    result := result.push ⟨kind,data⟩
    current := next
  current.done
  return result

def uints (c : Cursor) (s : Slice) : Except Error (List Nat) := do
  if s.length == 0 || s.length % 2 != 0 then throw .malformed
  let mut cur := c.sub s
  let mut result := []
  for _ in List.range (s.length/2) do
    let (n,next) ← cur.uint 2
    result := n :: result
    cur := next
  return result.reverse

def groupBit : Nat → Nat | 29 => 1 | 23 => 2 | _ => 0
def signatureBit : Nat → Nat | 0x0403 => 1 | 0x0804 => 2 | 0x0401 => 4 | 0x0807 => 8 | _ => 0

def share (c : Cursor) (v : View) : Except Error (View × Cursor × Nat) := do
  let (group,c) ← c.uint 2
  let (data,c) ← c.vector 2 1
  if (group == 29 && data.length != 32) || (group == 23 && data.length != 65) then
    throw .malformed
  if group == 23 && (data.bytes c.input)[0]! != 4 then throw .malformed
  let v := if group == 29 then v.set .x25519 data
    else if group == 23 then v.set .p256 data else v
  return ({v with selectedGroup := group, shareCount := v.shareCount+1},c,group)

def keyShares (c : Cursor) (v : View) : Except Error View := do
  if v.hrr then
    let (group,c) ← c.uint 2
    c.done
    return {v with selectedGroup := group}
  if v.kind == 2 then
    let (v,c,_) ← share c v
    c.done
    return v
  let (s,outer) ← c.vector 2 0
  outer.done
  let mut cur := c.sub s
  let mut view := v
  let mut seen : List Nat := []
  for _ in List.range (s.length/5) do
    if cur.pos == cur.stop then break
    let (next,c,group) ← share cur view
    if seen.contains group then throw .duplicate
    seen := group :: seen
    cur := c
    view := next
  cur.done
  return {view with selectedGroup := 0}

def protocolNames (c : Cursor) (v : View) : Except Error View := do
  let (s,outer) ← c.vector 2 2
  outer.done
  let mut cur := c.sub s
  let mut count := 0
  let mut matched := 0
  for _ in List.range (s.length/2) do
    if cur.pos == cur.stop then break
    let (name,next) ← cur.vector 1 1
    if name.bytes c.input == "libp2p".toUTF8.data then matched := matched+1
    count := count+1
    cur := next
  cur.done
  if v.kind == 8 && count != 1 then throw .malformed
  return {v with alpnMatches := matched}

def typedExtension (c : Cursor) (v : View) (e : Extension) : Except Error View := do
  let d := c.sub e.data
  if e.kind == 43 then
    let (s,next) ← if v.kind == 1 then d.vector 1 2 else d.take 2
    next.done
    let values ← uints c s
    if v.kind == 2 && values != [0x0304] then throw .profile
    return {(v.set .versions s) with versionMask := if values.contains 0x0304 then 1 else 0}
  if e.kind == 10 || e.kind == 13 || e.kind == 50 then
    let (s,next) ← d.vector 2 2
    next.done
    let values ← uints c s
    let f := if e.kind == 10 then Field.groups else if e.kind == 13 then .signatures else .certSignatures
    let v := v.set f s
    if e.kind == 10 then return {v with groupMask := values.foldl (fun m x => m ||| groupBit x) 0}
    if e.kind == 13 then return {v with signatureMask := values.foldl (fun m x => m ||| signatureBit x) 0}
    return v
  if e.kind == 51 then keyShares d (v.set .shares e.data)
  else if e.kind == 16 then protocolNames d (v.set .alpn e.data)
  else if e.kind == 57 then pure (v.set .transportParams e.data)
  else if e.kind == 44 then do
    let (s,next) ← d.vector 2 1
    next.done
    return v.set .cookie s
  else pure v

def extensionContext (v : View) (kind : Nat) : Except Error Unit := do
  if v.kind == 2 then
    if kind != 43 && kind != 51 && !(v.hrr && kind == 44) then throw .unsupported
  if (kind == 43 || kind == 51) && v.kind != 1 && v.kind != 2 then throw .malformed
  if kind == 44 && v.kind != 1 && !(v.kind == 2 && v.hrr) then throw .malformed
  if (kind == 13 || kind == 50) && v.kind != 1 && v.kind != 13 then throw .malformed
  if (kind == 16 || kind == 57 || kind == 10) && v.kind != 1 && v.kind != 8 then
    throw .malformed
  if kind == 42 && v.kind != 1 && v.kind != 4 then throw .malformed

/-- Only recognized handshake contexts are interpreted. Unrecognized server
extensions are retained, and MUST be checked for solicitation by integration.
SNI is ignored on receive; emitters reject ClientHello SNI separately. -/
def interpretExtensions (c : Cursor) (v : View) (s : Slice) : Except Error View := do
  let entries ← extensions (c.sub s)
  let mut view := v.set .extensions s
  for e in entries do
    extensionContext v e.kind
    if e.kind == 0 && v.kind == 1 then view := {view with sniPresent := true}
    view ← typedExtension c view e
  return view

end Libp2pAsm.Spec.Tls
