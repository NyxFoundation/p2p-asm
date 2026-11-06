import Libp2pAsm.Spec.Quic.Wire.Basic

namespace Libp2pAsm.Spec.Quic.Wire

structure PreferredAddress where
  raw : View
  ipv4 : View
  port4 : Nat
  ipv6 : View
  port6 : Nat
  cid : View
  token : View
  deriving Repr, BEq, DecidableEq

inductive Parameter where
  | integer (value : Nat)
  | view (bytes : View)
  | disableMigration
  | preferred (address : PreferredAddress)
  deriving Repr, BEq, DecidableEq

structure Transport where
  consumed : Nat
  count : Nat
  known : List (Nat × Parameter)
  deriving Repr, BEq, DecidableEq

def parameterDefault (id : Nat) : Nat :=
  if id == 3 then 65527 else if id == 10 then 3 else if id == 11 then 25
  else if id == 14 then 2 else 0

def Transport.value (t : Transport) (id : Nat) : Nat :=
  match t.known.lookup id with
  | some (.integer n) => n | some .disableMigration => 1 | _ => parameterDefault id

def Transport.words (t : Transport) : List Nat := Id.run do
  let mut words := Array.replicate 64 0
  words := (words.set! 0 t.consumed).set! 1 t.count
  for id in [3,10,11,14] do words := words.set! (4+2*id) (parameterDefault id)
  for (id,p) in t.known do
    words := words.set! 2 (words[2]! + 2^id)
    let (a,b) := match p with
      | .integer n => (n,0) | .view v => (v.offset,v.length)
      | .disableMigration => (1,0) | .preferred a => (a.raw.offset,a.raw.length)
    words := (words.set! (4+2*id) a).set! (5+2*id) b
    if let .preferred a := p then
      let fields := [a.ipv4.offset,4,a.port4,a.ipv6.offset,16,a.port6,
        a.cid.offset,a.cid.length,a.token.offset,16]
      for (v,i) in fields.zipIdx do words := words.set! (40+i) v
  return words.toList

private def readAt (v : View) (n width : Nat) : Parser Nat := do
  let bs := (← get).bytes.extract (v.offset+n) (v.offset+n+width)
  return bs.foldl (fun a b => a*256+b.toNat) 0

private def preferred (v : View) : Parser Parameter := do
  require (v.length ≥ 41)
  let n ← readAt v 24 1
  require (0 < n && n ≤ 20 && v.length == 41+n)
  return .preferred ⟨v,⟨v.offset,4⟩,← readAt v 4 2,⟨v.offset+6,16⟩,
    ← readAt v 22 2,⟨v.offset+25,n⟩,⟨v.offset+25+n,16⟩⟩

def integerValid (id value : Nat) : Bool :=
  value ≤ maxVarint && (id != 3 || 1200 ≤ value) &&
  (id != 8 && id != 9 || value ≤ 2^60) && (id != 10 || value ≤ 20) &&
  (id != 11 || value < 2^14) && (id != 14 || 2 ≤ value)

private def knownParameter (id : Nat) (v : View) (server : Bool) : Parser Parameter := do
  require (server || ![0,2,13,16].contains id) 9
  if [0,15,16].contains id then
    require (v.length ≤ 20)
    return .view v
  if id == 2 then
    require (v.length == 16)
    return .view v
  if id == 12 then
    require (v.length == 0)
    return .disableMigration
  if id == 13 then return ← preferred v
  let bytes := (← get).bytes.extract v.offset (v.offset+v.length)
  match Codec.QuicVarint.decode bytes.toList with
  | .error _ => fail 2
  | .ok d =>
    require (d.consumed == v.length) 2
    require (integerValid id d.value)
    return .integer d.value

private def transportParser (server : Bool) (capacity : Nat) : Parser (List (Nat × Parameter) × Nat) := do
  let mut seen : List Nat := []
  let mut known : List (Nat × Parameter) := []
  for _ in List.range (min capacity ((← get).bytes.size/2+1)) do
    if (← remaining) == 0 then return (known.reverse,seen.length)
    let id ← integer
    let n ← integer
    require (!seen.contains id) 8
    seen := id::seen
    let v ← take n
    if id ≤ 16 then known := (id,← knownParameter id v server)::known
  require ((← remaining) == 0) 5
  return (known.reverse,seen.length)

/-- ALL IDs enter duplicate detection. Capacity bounds the quadratic scan count.
CID presence and cross-message matching are caller connection-state obligations. -/
def parseTransport (bytes : Array UInt8) (server : Bool) (capacity : Nat) : Except Error Transport := do
  let ((known,count),n) ← run (transportParser server capacity) bytes
  return ⟨n,count,known⟩

structure ProfileParameters where
  idleTimeout : Nat
  maxUdpPayload : Nat
  maxData : Nat
  bidiLocal : Nat
  bidiRemote : Nat
  bidiStreams : Nat
  ackDelayExponent : Nat
  maxAckDelay : Nat
  activeCidLimit : Nat
  initialScid : List UInt8
  originalDcid : Option (List UInt8) := none
  retryScid : Option (List UInt8) := none
  resetToken : Option (List UInt8) := none
  deriving Repr

private def encodeParameter (id : Nat) (value : List UInt8) : Except Error (List UInt8) := do
  return (← encInt id) ++ (← encInt value.length) ++ value

/-- Profile advertises supplied resource values, no migration, zero uni streams/data,
and no preferred address or extension. Server CID linkage is supplied by the caller. -/
def encodeProfile (p : ProfileParameters) (server : Bool) (capacity : Nat) :
    Except Error (List UInt8) := do
  let entries := [(1,p.idleTimeout),(3,p.maxUdpPayload),(4,p.maxData),(5,p.bidiLocal),
    (6,p.bidiRemote),(7,0),(8,p.bidiStreams),(9,0),(10,p.ackDelayExponent),
    (11,p.maxAckDelay),(14,p.activeCidLimit)]
  let mut bs := []
  for (id,n) in entries do
    unless integerValid id n do throw ⟨3,0⟩
    bs := bs ++ (← encodeParameter id (← encInt n))
  bs := bs ++ (← encodeParameter 12 []) ++ (← encodeParameter 15 p.initialScid)
  for (id,value) in [(0,p.originalDcid),(16,p.retryScid),(2,p.resetToken)] do
    if let some v := value then
      unless server do throw ⟨9,0⟩
      bs := bs ++ (← encodeParameter id v)
  let _ ← parseTransport bs.toArray server 17
  bounded capacity bs

end Libp2pAsm.Spec.Quic.Wire
