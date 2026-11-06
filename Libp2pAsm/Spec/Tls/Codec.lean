import Libp2pAsm.Spec.Tls.Extensions

namespace Libp2pAsm.Spec.Tls

def hello (c : Cursor) (v : View) : Except Error View := do
  let (legacy,c) ← c.uint 2
  if legacy != 0x0303 then throw .profile
  let (random,c) ← c.take 32
  let (session,c) ← c.vector 1 0
  if session.length > 32 then throw .profile
  let v := (v.set .random random).set .session session
  let v := {v with legacyVersion := legacy}
  let v := {v with hrr := v.kind == 2 && random.bytes c.input == hrrRandom}
  let (v,c) ← if v.kind == 1 then do
    let (suites,c) ← c.vector 2 2
    let values ← uints c suites
    let (compression,c) ← c.vector 1 1
    if compression.bytes c.input != #[0] then throw .profile
    pure ({((v.set .suites suites).set .compression compression) with
      cipherSuite := if values.contains 0x1301 then 0x1301 else 0},c)
    else do
      let (suite,c) ← c.uint 2
      let (compression,c) ← c.uint 1
      if suite != 0x1301 || compression != 0 then throw .profile
      pure ({v with cipherSuite := suite, compression := compression},c)
  let (ext,c) ← c.vector 2 0
  c.done
  interpretExtensions c v ext

def certRequest (c : Cursor) (v : View) : Except Error View := do
  let (context,c) ← c.vector 1 0
  let (ext,c) ← c.vector 2 0
  c.done
  interpretExtensions c (v.set .requestContext context) ext

/-- Full uint24 list lengths. All entries are checked even though the libp2p
profile admits exactly one. Views expose the list and the first entry. -/
def certificate (c : Cursor) (v : View) : Except Error View := do
  let (context,c) ← c.vector 1 0
  let (list,c) ← c.vector 3 0
  c.done
  let mut cur := c.sub list
  let mut view := (v.set .requestContext context).set .certificates list
  for _ in List.range (list.length/6) do
    if cur.pos == cur.stop then break
    let (data,next) ← cur.vector 3 1
    let (ext,next) ← next.vector 2 0
    let entries ← extensions (cur.sub ext)
    for e in entries do extensionContext view e.kind
    if view.certificateCount == 0 then
      view := (view.set .certificate data).set .certificateExtensions ext
    view := {view with certificateCount := view.certificateCount+1}
    cur := next
  cur.done
  return view

def ticket (c : Cursor) (v : View) : Except Error View := do
  let (lifetime,c) ← c.uint 4
  let (age,c) ← c.uint 4
  if lifetime > 604800 then throw .profile
  let (nonce,c) ← c.vector 1 0
  let (ticket,c) ← c.vector 2 1
  let (ext,c) ← c.vector 2 0
  c.done
  let entries ← extensions (c.sub ext)
  for e in entries do
    extensionContext v e.kind
    if e.kind == 42 && e.data.length != 4 then throw .malformed
  return {((v.set .ticketNonce nonce).set .ticket ticket).set .extensions ext with
    lifetime := lifetime, ageAdd := age}

def message (c : Cursor) (v : View) : Except Error View := do
  if v.kind == 1 || v.kind == 2 then hello c v
  else if v.kind == 8 then do
    let (ext,c) ← c.vector 2 0
    c.done
    interpretExtensions c v ext
  else if v.kind == 13 then certRequest c v
  else if v.kind == 11 then certificate c v
  else if v.kind == 15 then do
    let (scheme,c) ← c.uint 2
    let (signature,c) ← c.vector 2 1
    c.done
    if scheme != 0x0403 && scheme != 0x0804 && scheme != 0x0807 then throw .profile
    return {(v.set .signature signature) with signatureScheme := scheme}
  else if v.kind == 20 then do
    let (data,c) ← c.take 32
    c.done
    return v.set .verifyData data
  else if v.kind == 4 then ticket c v
  else throw .unsupported

def profile (v : View) : Except Error Unit := do
  if v.kind == 1 then
    if v.cipherSuite != 0x1301 || v.versionMask != 1 || v.groupMask == 0 ||
        v.signatureMask &&& 11 == 0 || v.alpnMatches == 0 ||
        (v.get .transportParams).offset == 0 || (v.get .shares).offset == 0 then throw .profile
    if (v.get .x25519).length > 0 && v.groupMask &&& 1 == 0 then throw .profile
    if (v.get .p256).length > 0 && v.groupMask &&& 2 == 0 then throw .profile
  if v.kind == 2 then
    if v.versionMask != 1 then throw .profile
    if v.hrr then
      if (v.get .shares).offset == 0 && (v.get .cookie).offset == 0 then throw .profile
      if (v.get .shares).offset != 0 && groupBit v.selectedGroup == 0 then throw .profile
    else if v.shareCount != 1 || groupBit v.selectedGroup == 0 then throw .profile
  if v.kind == 8 && (v.alpnMatches != 1 || (v.get .transportParams).offset == 0) then throw .profile
  if v.kind == 13 && ((v.get .requestContext).length != 0 || v.signatureMask &&& 11 == 0) then
    throw .profile
  if v.kind == 11 && ((v.get .requestContext).length != 0 || v.certificateCount != 1) then
    throw .profile

/-- Decode one message; consumed excludes any concatenated following message.
Status needMore only denotes an incomplete OUTER message; inner overruns of a
complete message are malformed. Profile=false supports published generic TLS
traces but still enforces TLS1.3 legacy fields and SHA256 Finished size. -/
def decode (input : Bytes) (limit : Nat) (libp2p : Bool := true) : Except Error View := do
  let (kind,c) ← frame input limit
  let obligations := if kind == 1 then 8 else if kind == 2 then 3
    else if kind == 8 then 9 else if kind == 11 || kind == 15 then 5
    else if kind == 13 || kind == 4 then 1 else 0
  let v ← message c {kind := kind, consumed := c.stop, obligations := obligations}
  if libp2p then profile v
  return v

/-- Checked raw-body encoder; helpers above construct uint8/16/24 vectors.
The decoder also validates the completed body before it is returned. -/
def encode (kind : Nat) (body : Bytes) (limit : Nat) (libp2p : Bool := true) : Except Error Bytes := do
  if kind > 255 || body.size ≥ 2^24 then throw .malformed
  if body.size > limit then throw .limit
  let raw := #[kind.toUInt8] ++ be 3 body.size ++ body
  let view ← decode raw limit libp2p
  if kind == 1 then
    let entries ← extensions ⟨raw,(view.get .extensions).offset,view.consumed⟩
    if entries.any (·.kind == 0) then throw .profile
  return raw

/-- QUIC integration must reject TLS records at its input boundary, before the
handshake codec. Finished and TLS ChangeCipherSpec both have byte value 20,
so no raw-byte heuristic can distinguish their enclosing protocols. -/
def admitQuic (isRecord : Bool) (handshakeType : Nat) : Except Error Unit := do
  if isRecord || handshakeType == 24 then throw .unsupported

end Libp2pAsm.Spec.Tls
