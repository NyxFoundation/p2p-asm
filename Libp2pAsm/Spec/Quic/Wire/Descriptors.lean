import Libp2pAsm.Spec.Quic.Wire.Packet
import Libp2pAsm.Spec.Quic.Wire.FrameEncode
import Libp2pAsm.Spec.Quic.Wire.Transport

namespace Libp2pAsm.Spec.Quic.Wire.Descriptors

def word (bytes : Array UInt8) (i : Nat) : Except Error Nat := do
  let bs ← viewBytes bytes ⟨8*i,8⟩
  return (bs.zipIdx.map fun (b,j) => b.toNat*256^j).sum

def view (bytes : Array UInt8) (i : Nat) : Except Error View := do
  return ⟨← word bytes i, ← word bytes (i+1)⟩

def data (bytes : Array UInt8) (i : Nat) : Except Error (List UInt8) := do
  viewBytes bytes (← view bytes i)

private def ack (bs : Array UInt8) (ecn : Bool) (capacity : Nat) : Except Error FrameBody := do
  let n ← word bs 4
  unless n < capacity do throw ⟨5,0⟩
  unless 144 ≤ bs.size && n ≤ (bs.size-144)/16 do throw ⟨1,0⟩
  let ranges ← (List.range (n+1)).mapM fun j => do
    pure (AckRange.mk (← word bs (16+2*j)) (← word bs (17+2*j)))
  let ec ← if ecn then do pure (some (← word bs 6, ← word bs 7, ← word bs 8)) else pure none
  return .ack ⟨← word bs 2,← word bs 3,← word bs 5,ranges,{},ec⟩

def frame (bs : Array UInt8) (capacity : Nat) : Except Error FrameBody := do
  let t ← word bs 1
  if 8 ≤ t && t ≤ 15 then
    return .stream (← word bs 2) (← word bs 3) (t%2 == 1) (t/4%2 == 1)
      (t/2%2 == 1) (← view bs 4)
  match t with
  | 0 => pure .padding | 1 => pure .ping | 30 => pure .handshakeDone
  | 2 => ack bs false capacity | 3 => ack bs true capacity
  | 4 => return .resetStream (← word bs 2) (← word bs 3) (← word bs 4)
  | 5 => return .stopSending (← word bs 2) (← word bs 3)
  | 6 => return .crypto (← word bs 2) (← view bs 3)
  | 7 => return .newToken (← view bs 2)
  | 16 => return .maxData (← word bs 2)
  | 17 => return .maxStreamData (← word bs 2) (← word bs 3)
  | 18 | 19 => return .maxStreams (t == 19) (← word bs 2)
  | 20 => return .dataBlocked (← word bs 2)
  | 21 => return .streamDataBlocked (← word bs 2) (← word bs 3)
  | 22 | 23 => return .streamsBlocked (t == 23) (← word bs 2)
  | 24 => return .newConnectionId (← word bs 2) (← word bs 3) (← view bs 4) (← view bs 6)
  | 25 => return .retireConnectionId (← word bs 2)
  | 26 => return .pathChallenge (← view bs 2) | 27 => return .pathResponse (← view bs 2)
  | 28 | 29 => return .connectionClose (t == 29) (← word bs 2) (← word bs 3) (← view bs 4)
  | _ => throw ⟨7,0⟩

def packet (bs : Array UInt8) : Except Error PacketBuild := do
  let flags ← word bs 2
  unless flags ||| 36 == 36 do throw ⟨3,0⟩
  let k ← word bs 1
  let kind ← match k with
    | 0 => pure PacketKind.short | 1 => pure .initial | 2 => pure .zeroRtt
    | 3 => pure .handshake | 4 => pure .retry | 5 => pure .versionNegotiation
    | _ => throw ⟨10,0⟩
  return {
    kind := kind
    dcid := ← data bs 4
    scid := ← data bs 6
    token := ← data bs 8,
    payload := ← data bs 12
    pnLength := ← word bs 14
    truncatedPN := ← word bs 15,
    spin := flags / 32 % 2 == 1
    keyPhase := flags / 4 % 2 == 1}

def profile (bs : Array UInt8) : Except Error ProfileParameters := do
  let mask ← word bs 2
  unless mask < 2^17 && mask / 2^13 % 2 == 0 do throw ⟨10,0⟩
  let optional := fun id => if mask / 2^id % 2 == 1 then
    (data bs (4+2*id)).map some else pure none
  return {
    idleTimeout := ← word bs 6
    maxUdpPayload := ← word bs 10,
    maxData := ← word bs 12
    bidiLocal := ← word bs 14
    bidiRemote := ← word bs 16,
    bidiStreams := ← word bs 20
    ackDelayExponent := ← word bs 24,
    maxAckDelay := ← word bs 26
    activeCidLimit := ← word bs 32,
    initialScid := ← data bs 34
    originalDcid := ← optional 0,
    retryScid := ← optional 16
    resetToken := ← optional 2}

def encode (kind : Nat) (bs : Array UInt8) (server : Bool) (bound capacity : Nat) :
    Except Error (List UInt8) :=
  (do
    unless (if kind == 2 then 512 else 128) ≤ bs.size do throw (⟨1,0⟩ : Error)
    if kind == 0 then encodePacket (← packet bs) capacity
    else if kind == 1 then encodeFrame bs (← frame bs bound) bound capacity
    else encodeProfile (← profile bs) server capacity).mapError (fun (e : Error) => {e with offset := 0})

end Libp2pAsm.Spec.Quic.Wire.Descriptors
