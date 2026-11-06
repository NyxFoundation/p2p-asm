import Libp2pAsm.Spec.Quic.Wire.Basic

namespace Libp2pAsm.Spec.Quic.Wire

structure AckRange where
  low : Nat
  high : Nat
  deriving Repr, BEq, DecidableEq

structure Ack where
  largest : Nat
  delay : Nat
  firstRange : Nat
  ranges : List AckRange
  encodedRanges : View
  ecn : Option (Nat × Nat × Nat)
  deriving Repr, BEq, DecidableEq

inductive FrameBody where
  | padding | ping
  | ack (value : Ack)
  | resetStream (stream error finalSize : Nat)
  | stopSending (stream error : Nat)
  | crypto (offset : Nat) (data : View)
  | newToken (data : View)
  | stream (id offset : Nat) (fin hasOffset hasLength : Bool) (data : View)
  | maxData (value : Nat)
  | maxStreamData (stream value : Nat)
  | maxStreams (uni : Bool) (value : Nat)
  | dataBlocked (value : Nat)
  | streamDataBlocked (stream value : Nat)
  | streamsBlocked (uni : Bool) (value : Nat)
  | newConnectionId (sequence retirePriorTo : Nat) (cid token : View)
  | retireConnectionId (sequence : Nat)
  | pathChallenge (data : View) | pathResponse (data : View)
  | connectionClose (application : Bool) (error frameType : Nat) (reason : View)
  | handshakeDone
  deriving Repr, BEq, DecidableEq

def FrameBody.tag : FrameBody → Nat
  | .padding => 0 | .ping => 1 | .ack a => if a.ecn.isSome then 3 else 2
  | .resetStream .. => 4 | .stopSending .. => 5 | .crypto .. => 6 | .newToken .. => 7
  | .stream _ _ fin off len _ => 8+(if fin then 1 else 0)+(if off then 4 else 0)+(if len then 2 else 0)
  | .maxData .. => 16 | .maxStreamData .. => 17 | .maxStreams uni _ => if uni then 19 else 18
  | .dataBlocked .. => 20 | .streamDataBlocked .. => 21
  | .streamsBlocked uni _ => if uni then 23 else 22
  | .newConnectionId .. => 24 | .retireConnectionId .. => 25
  | .pathChallenge .. => 26 | .pathResponse .. => 27
  | .connectionClose app .. => if app then 29 else 28 | .handshakeDone => 30

def FrameBody.fields : FrameBody → List Nat
  | .padding | .ping | .handshakeDone => []
  | .ack a => [a.largest,a.delay,a.ranges.length-1,a.firstRange,
      a.ecn.map (·.1) |>.getD 0, a.ecn.map (·.2.1) |>.getD 0,
      a.ecn.map (·.2.2) |>.getD 0,a.encodedRanges.offset,a.encodedRanges.length]
  | .resetStream s e f => [s,e,f] | .stopSending s e => [s,e]
  | .crypto off v => [off,v.offset,v.length] | .newToken v => [v.offset,v.length]
  | .stream id off _ _ _ v => [id,off,v.offset,v.length]
  | .maxData v | .maxStreams _ v | .dataBlocked v | .streamsBlocked _ v => [v]
  | .maxStreamData s v | .streamDataBlocked s v => [s,v]
  | .newConnectionId s r c t => [s,r,c.offset,c.length,t.offset,t.length]
  | .retireConnectionId s => [s]
  | .pathChallenge v | .pathResponse v => [v.offset,v.length]
  | .connectionClose _ e t v => [e,t,v.offset,v.length]

structure Frame where
  consumed : Nat
  body : FrameBody
  deriving Repr, BEq, DecidableEq

def Frame.words (f : Frame) : List Nat :=
  let fields := f.body.fields
  let extra := match f.body with
    | .ack a => a.ranges.flatMap fun r => [r.low,r.high]
    | _ => []
  [f.consumed,f.body.tag] ++ fields ++ List.replicate (14-fields.length) 0 ++ extra

private def ackParser (ecn : Bool) (capacity : Nat) : Parser FrameBody := do
  let largest ← integer
  let delay ← integer
  let count ← integer
  let firstRange ← integer
  require (firstRange ≤ largest)
  require (count ≤ (← remaining)/2) 1
  require (count < capacity) 5
  let start := (← get).pos
  let mut low := largest-firstRange
  let mut ranges := [AckRange.mk low largest]
  for _ in List.range count do
    let gap ← integer
    let size ← integer
    require (gap+2 ≤ low)
    let high := low-gap-2
    require (size ≤ high)
    low := high-size
    ranges := ⟨low,high⟩::ranges
  let encodedRanges : View := ⟨start,(← get).pos-start⟩
  let ec ← if ecn then do pure (some (← integer, ← integer, ← integer)) else pure none
  return .ack ⟨largest,delay,firstRange,ranges.reverse,encodedRanges,ec⟩

private def streamParser (t : Nat) : Parser FrameBody := do
  let id ← integer
  let off ← if t / 4 % 2 == 1 then integer else pure 0
  let n ← if t / 2 % 2 == 1 then integer else remaining
  require (n ≤ maxVarint-off)
  return .stream id off (t % 2 == 1) (t / 4 % 2 == 1) (t / 2 % 2 == 1) (← take n)

private def newCid : Parser FrameBody := do
  let s ← integer
  let r ← integer
  require (r ≤ s)
  let n ← byte
  require (0 < n && n ≤ 20)
  let cid ← take n
  return .newConnectionId s r cid (← take 16)

private def streamCount : Parser Nat := do
  let n ← integer
  require (n ≤ 2^60)
  return n

private def frameParser (capacity : Nat) : Parser FrameBody := do
  let t ← integer
  if 8 ≤ t && t ≤ 15 then return ← streamParser t
  match t with
  | 0 => pure .padding | 1 => pure .ping
  | 2 => ackParser false capacity | 3 => ackParser true capacity
  | 4 => return .resetStream (← integer) (← integer) (← integer)
  | 5 => return .stopSending (← integer) (← integer)
  | 6 =>
    let off ← integer
    let n ← integer
    require (n ≤ maxVarint-off)
    return .crypto off (← take n)
  | 7 =>
    let n ← integer
    require (n > 0)
    return .newToken (← take n)
  | 16 => return .maxData (← integer)
  | 17 => return .maxStreamData (← integer) (← integer)
  | 18 => return .maxStreams false (← streamCount)
  | 19 => return .maxStreams true (← streamCount)
  | 20 => return .dataBlocked (← integer)
  | 21 => return .streamDataBlocked (← integer) (← integer)
  | 22 => return .streamsBlocked false (← streamCount)
  | 23 => return .streamsBlocked true (← streamCount)
  | 24 => newCid | 25 => return .retireConnectionId (← integer)
  | 26 => return .pathChallenge (← take 8) | 27 => return .pathResponse (← take 8)
  | 28 | 29 =>
    let e ← integer
    let ft ← if t == 28 then integer else pure 0
    return .connectionClose (t == 29) e ft (← take (← integer))
  | 30 => pure .handshakeDone
  | _ => fail 7

/-- Nonminimal type reception is tolerated (RFC 9000 12.4 MAY reject); output is minimal. -/
def parseFrame (bytes : Array UInt8) (ackCapacity : Nat) : Except Error Frame := do
  let (body,n) ← run (frameParser ackCapacity) bytes
  return ⟨n,body⟩

inductive Level where
  | initial | handshake | zeroRtt | oneRtt
  deriving Repr, BEq, DecidableEq

/-- Sender role; caller enforces its independent policy to reject all 0-RTT. -/
def permitted (tag : Nat) (level : Level) (server : Bool) : Bool :=
  let role := !((tag == 7 || tag == 30) && !server) && !(level == .zeroRtt && server)
  let inLevel := match level with
    | .initial | .handshake => [0,1,2,3,6,28].contains tag
    | .zeroRtt => tag ≤ 29 && ![2,3,6,7,25,27].contains tag
    | .oneRtt => tag ≤ 30
  role && inLevel

def ackEliciting (tag : Nat) : Bool := ![0,2,3,28,29].contains tag
def countsInFlight (tag : Nat) : Bool := ![2,3,28,29].contains tag

end Libp2pAsm.Spec.Quic.Wire
