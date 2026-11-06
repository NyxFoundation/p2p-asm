import Libp2pAsm.Spec.Quic.Wire.Frame

namespace Libp2pAsm.Spec.Quic.Wire

private def ints (values : List Nat) : Except Error (List UInt8) := do
  return (← values.mapM encInt).flatten

private def countInt (n : Nat) : Except Error (List UInt8) :=
  if n ≤ 2^60 then encInt n else .error ⟨3,0⟩

private def offsetCheck (offset length : Nat) : Except Error Unit :=
  if offset ≤ maxVarint ∧ length ≤ maxVarint-offset then .ok () else .error ⟨3,0⟩

private def encodeAck (a : Ack) (capacity : Nat) : Except Error (List UInt8) := do
  unless a.ranges.length > 0 && a.ranges.length ≤ capacity do throw ⟨5,0⟩
  let first := a.ranges.headD ⟨0,0⟩
  unless a.firstRange ≤ a.largest && first.high == a.largest &&
      first.low == a.largest-a.firstRange do throw ⟨3,0⟩
  let mut bytes ← ints [a.largest,a.delay,a.ranges.length-1,a.firstRange]
  let mut low := first.low
  for r in a.ranges.tail do
    unless r.low ≤ r.high && r.high ≤ maxVarint && r.high+2 ≤ low do throw ⟨3,0⟩
    bytes := bytes ++ (← ints [low-r.high-2,r.high-r.low])
    low := r.low
  if let some (a,b,c) := a.ecn then bytes := bytes ++ (← ints [a,b,c])
  return bytes

private def encodeStream (source : Array UInt8) (id off : Nat) (hasOff hasLen : Bool)
    (v : View) : Except Error (List UInt8) := do
  offsetCheck off v.length
  unless hasOff || off == 0 do throw ⟨3,0⟩
  let offBytes ← if hasOff then encInt off else pure []
  let lenBytes ← if hasLen then encInt v.length else pure []
  return (← encInt id) ++ offBytes ++ lenBytes ++ (← viewBytes source v)

private def encodeNewCid (source : Array UInt8) (s r : Nat) (cid token : View) :
    Except Error (List UInt8) := do
  unless r ≤ s && 0 < cid.length && cid.length ≤ 20 && token.length == 16 do throw ⟨3,0⟩
  return (← ints [s,r]) ++ [cid.length.toUInt8] ++ (← viewBytes source cid) ++
    (← viewBytes source token)

private def encodeBody (source : Array UInt8) (capacity : Nat) : FrameBody → Except Error (List UInt8)
  | .padding | .ping | .handshakeDone => pure []
  | .ack a => encodeAck a capacity
  | .resetStream s e f => ints [s,e,f] | .stopSending s e => ints [s,e]
  | .crypto off v => do
    offsetCheck off v.length
    return (← ints [off,v.length]) ++ (← viewBytes source v)
  | .newToken v => do
    unless v.length > 0 do throw ⟨3,0⟩
    return (← encInt v.length) ++ (← viewBytes source v)
  | .stream id off _ ho hl v => encodeStream source id off ho hl v
  | .maxData n | .dataBlocked n | .retireConnectionId n => encInt n
  | .maxStreamData s n | .streamDataBlocked s n => ints [s,n]
  | .maxStreams _ n | .streamsBlocked _ n => countInt n
  | .newConnectionId s r c t => encodeNewCid source s r c t
  | .pathChallenge v | .pathResponse v => do
    unless v.length == 8 do throw ⟨3,0⟩
    viewBytes source v
  | .connectionClose app e t reason => do
    let typeBytes ← if app then pure [] else encInt t
    return (← encInt e) ++ typeBytes ++ (← encInt reason.length) ++ (← viewBytes source reason)

def encodeFrame (source : Array UInt8) (body : FrameBody) (ackCapacity capacity : Nat) :
    Except Error (List UInt8) := do
  bounded capacity ([body.tag.toUInt8] ++ (← encodeBody source ackCapacity body))

end Libp2pAsm.Spec.Quic.Wire
