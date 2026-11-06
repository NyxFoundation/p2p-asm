import Libp2pAsm.Spec.Crypto.Quic.Basic

namespace Libp2pAsm.Spec.Crypto.Quic

def hpMask (keys sample : Array UInt8) : Except Error (Array UInt8) := do
  if keys.size != 44 || sample.size != 16 then throw .length
  let hp := keys.extract 28 44
  if h : hp.size = 16 then
    return (AES.encrypt ⟨hp, h⟩ (GCM.blockOf sample)).toArray.extract 0 5
  else throw .length

def maskFirst (b mask : UInt8) : UInt8 := b ^^^ (mask &&& (if b &&& 0x80 == 0 then 0x1f else 0x0f))

def maskPN (packet mask : Array UInt8) (offset count : Nat) : Array UInt8 :=
  (List.range count).foldl (fun bs i => bs.set! (offset+i) (bs[offset+i]! ^^^ mask[i+1]!)) packet

/-- Seal takes explicit header length, PN offset and full PN, writes its low bytes
into the staged header. The caller owns full header/version/packet-type parsing. -/
def protect (keys input : Array UInt8) (offset headerLength pn limit : Nat) :
    Except Error (Array UInt8) := do
  if pn ≥ 2^62 then throw .number
  if keys.size != 44 || input.size > limit || limit > GCM.maxMessageBytes then throw .length
  if offset == 0 || offset ≥ input.size then throw .header
  let count := (input[0]!.toNat % 4)+1
  if headerLength != offset+count || headerLength > input.size then throw .header
  if input.size+16 < offset+20 then throw .sample
  let header := input.extract 0 offset ++ (Sha2.encodeBE count pn).toArray
  let n ← nonce (keys.extract 16 28) pn
  let payload ← (GCM.seal (keys.extract 0 16) n header
    (input.extract headerLength input.size)).mapError (fun _ => .crypto)
  let packet := header ++ payload
  let mask ← hpMask keys (packet.extract (offset+4) (offset+20))
  return maskPN (packet.set! 0 (maskFirst packet[0]! mask[0]!)) mask offset count

structure Opened where
  number : Nat
  headerLength : Nat
  packet : Array UInt8
  deriving BEq, Repr

def unprotect (keys packet : Array UInt8) (offset expected limit : Nat) : Except Error Opened := do
  if expected > 2^62 then throw .number
  if keys.size != 44 || packet.size > limit || limit > GCM.maxMessageBytes then throw .length
  if offset == 0 || offset ≥ packet.size then throw .header
  if packet.size < offset+20 then throw .sample
  let mask ← hpMask keys (packet.extract (offset+4) (offset+20))
  let first := maskFirst packet[0]! mask[0]!
  let count := first.toNat % 4+1
  let header := maskPN ((packet.extract 0 (offset+count)).set! 0 first) mask offset count
  let truncated := (Sha2.readWord 64 (header.extract offset header.size).toList).toNat
  let pn ← reconstruct expected truncated count
  let n ← nonce (keys.extract 16 28) pn
  let plain ← (GCM.open (keys.extract 0 16) n header
    (packet.extract header.size packet.size)).mapError (fun _ => .authentication)
  return ⟨pn, header.size, header ++ plain⟩

end Libp2pAsm.Spec.Crypto.Quic
