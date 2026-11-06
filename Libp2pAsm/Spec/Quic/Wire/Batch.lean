import Libp2pAsm.Spec.Quic.Wire.Packet
import Libp2pAsm.Spec.Quic.Wire.Frame

namespace Libp2pAsm.Spec.Quic.Wire

def parseFrames (bytes : Array UInt8) (ackCapacity capacity : Nat) :
    Except Error (List (Nat × Frame)) := do
  let mut pos := 0
  let mut frames := []
  for _ in List.range (min capacity bytes.size) do
    if pos == bytes.size then return frames.reverse
    let f ← (parseFrame (bytes.extract pos bytes.size) ackCapacity).mapError
      (fun e => {e with offset := pos+e.offset})
    if f.consumed == 0 then throw ⟨2,pos⟩
    frames := (pos,f)::frames
    pos := pos+f.consumed
  if pos == bytes.size then return frames.reverse
  throw ⟨5,pos⟩

/-- Fixed-capacity descriptor table; unused slots and padding are zero. Views in
each record are relative to its recorded source base, never host pointers. -/
def batchWords (packets : Bool) (bytes : Array UInt8) (option capacity : Nat) :
    Except Error (List Nat) := do
  let records ← if packets then do
      pure ((← parsePackets bytes option capacity).map fun (off,p) => (off,p.words))
    else do pure ((← parseFrames bytes option capacity).map fun (off,f) => (off,f.words))
  let width := if packets then 18 else 18+2*option
  let body := records.flatMap fun (off,ws) => [off] ++ ws ++ List.replicate (width-1-ws.length) 0
  return [bytes.size,records.length] ++ body ++ List.replicate ((capacity-records.length)*width) 0

end Libp2pAsm.Spec.Quic.Wire
