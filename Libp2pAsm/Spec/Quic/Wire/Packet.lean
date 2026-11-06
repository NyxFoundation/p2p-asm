import Libp2pAsm.Spec.Quic.Wire.Basic

namespace Libp2pAsm.Spec.Quic.Wire

inductive PacketKind where
  | short | initial | zeroRtt | handshake | retry | versionNegotiation | unsupported
  deriving Repr, BEq, DecidableEq, Inhabited

def PacketKind.code : PacketKind → Nat
  | .short => 0 | .initial => 1 | .zeroRtt => 2 | .handshake => 3
  | .retry => 4 | .versionNegotiation => 5 | .unsupported => 6

/-- Unauthenticated envelope only. The low protected bits remain uninterpreted. -/
structure Packet where
  consumed : Nat := 0
  kind : PacketKind := .short
  first : Nat := 0
  version : Nat := 0
  dcid : View := {}
  scid : View := {}
  token : View := {}
  pnOffset : Nat := 0
  protectedLength : Nat := 0
  tail : View := {}
  deriving Repr, BEq, DecidableEq, Inhabited

def Packet.words (p : Packet) : List Nat :=
  [p.consumed,p.kind.code,p.first,p.version,p.dcid.offset,p.dcid.length,
   p.scid.offset,p.scid.length,p.token.offset,p.token.length,p.pnOffset,
   p.protectedLength,p.tail.offset,p.tail.length,0,0]

private def cid : Parser View := do
  let n ← byte
  require (n ≤ 20)
  take n

private def versionOne (p : Packet) : Parser Packet := do
  require (p.first / 64 % 2 == 1) 2
  let kind := p.first / 16 % 4
  if kind == 3 then
    require ((← remaining) ≥ 17) 1
    let token ← take ((← remaining)-16)
    let tag ← take 16
    return {p with kind := .retry, token := token, tail := tag}
  let token ← if kind == 0 then take (← integer) else pure ({} : View)
  let n ← integer
  require (n > 0) 2
  let payloadView ← take n
  let packetKind := if kind == 0 then PacketKind.initial else if kind == 1 then .zeroRtt else .handshake
  return {p with kind := packetKind, token := token, pnOffset := payloadView.offset, protectedLength := n}

private def packetParser (shortCidLength : Nat) : Parser Packet := do
  let first ← byte
  if first < 128 then
    require (shortCidLength ≤ 20) 10
    require (first / 64 % 2 == 1) 2
    let dcid ← take shortCidLength
    let pnOffset := (← get).pos
    let n ← remaining
    require (n > 0) 1
    let _ ← take n
    return {first, dcid, pnOffset, protectedLength := n}
  let version ← bigEndian 4
  let dcid ← cid
  let scid ← cid
  let p : Packet := {first, version, dcid, scid}
  if version == 0 then
    let n ← remaining
    require (n > 0 && n % 4 == 0) 2
    return {p with kind := .versionNegotiation, tail := ← take n}
  if version != 1 then
    return {p with kind := .unsupported, tail := ← take (← remaining)}
  versionOne p

def parsePacket (bytes : Array UInt8) (shortCidLength : Nat) : Except Error Packet := do
  let (p,n) ← run (packetParser shortCidLength) bytes
  return {p with consumed := n}

/-- Bounded coalescing caller. A final short/VN/Retry/unknown envelope consumes the rest. -/
def parsePackets (bytes : Array UInt8) (shortCidLength capacity : Nat) :
    Except Error (List (Nat × Packet)) := do
  let mut pos := 0
  let mut packets := []
  for _ in List.range (min capacity bytes.size) do
    if pos == bytes.size then return packets.reverse
    let p ← (parsePacket (bytes.extract pos bytes.size) shortCidLength).mapError
      (fun e => {e with offset := pos+e.offset})
    if p.consumed == 0 then throw ⟨2,pos⟩
    packets := (pos,p)::packets
    pos := pos+p.consumed
  if pos == bytes.size then return packets.reverse
  throw ⟨5,pos⟩

structure PacketBuild where
  kind : PacketKind
  dcid : List UInt8 := []
  scid : List UInt8 := []
  token : List UInt8 := []
  payload : List UInt8 := []
  pnLength : Nat := 1
  truncatedPN : Nat := 0
  spin : Bool := false
  keyPhase : Bool := false
  deriving Repr

private def longPrefix (kind : Nat) (p : PacketBuild) : List UInt8 :=
  [UInt8.ofNat (192+16*kind+p.pnLength-1),0,0,0,1,p.dcid.length.toUInt8] ++
  p.dcid ++ [p.scid.length.toUInt8] ++ p.scid

/-- Build unprotected bytes. Payload includes the caller-supplied AEAD/tag space.
No PN or key phase here is asserted authenticated; protection is the caller's job. -/
def encodePacket (p : PacketBuild) (capacity : Nat) : Except Error (List UInt8) := do
  unless p.dcid.length ≤ 20 && p.scid.length ≤ 20 do throw ⟨3,0⟩
  let ids := [p.dcid.length.toUInt8] ++ p.dcid ++ [p.scid.length.toUInt8] ++ p.scid
  if p.kind == .versionNegotiation then
    unless p.payload.length > 0 && p.payload.length % 4 == 0 do throw ⟨2,0⟩
    return ← bounded capacity ([128,0,0,0,0] ++ ids ++ p.payload)
  if p.kind == .retry then
    unless p.token.length > 0 && p.payload.length == 16 do throw ⟨3,0⟩
    return ← bounded capacity ([240,0,0,0,1] ++ ids ++ p.token ++ p.payload)
  if p.kind == .unsupported then throw ⟨10,0⟩
  unless 1 ≤ p.pnLength && p.pnLength ≤ 4 && p.truncatedPN < 256^p.pnLength do
    throw ⟨3,0⟩
  let pn := Codec.QuicVarint.bigEndian p.pnLength p.truncatedPN
  if p.kind == .short then
    let first := 64+(if p.spin then 32 else 0)+(if p.keyPhase then 4 else 0)+p.pnLength-1
    return ← bounded capacity ([first.toUInt8] ++ p.dcid ++ pn ++ p.payload)
  let headBytes := longPrefix (p.kind.code-1) p
  let tok ← if p.kind == .initial then do
    pure ((← encInt p.token.length) ++ p.token) else pure []
  bounded capacity (headBytes ++ tok ++ (← encInt (p.pnLength+p.payload.length)) ++ pn ++ p.payload)

end Libp2pAsm.Spec.Quic.Wire
