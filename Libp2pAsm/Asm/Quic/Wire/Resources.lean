import Libp2pAsm.Asm.Quic.Wire.Batch
import Libp2pAsm.Asm.Quic.Wire.PacketEncode
import Libp2pAsm.Asm.Quic.Wire.FrameEncode
import Libp2pAsm.Asm.Quic.Wire.TransportEncode
import Libp2pAsm.Asm.Quic.Wire.Permission

namespace Libp2pAsm.Asm.Quic.Wire

/-- Natural-number admission calculations, evaluated before conversion to ABI
words. These are structural ceilings, not a whole-program termination theorem. -/
def instructionBound (kind : String) (staticSize inputSize option capacity outputCap workCap : Nat) : Nat :=
  if kind == "permission" then staticSize+1 else
  if kind == "packet" then staticSize*(1+3*128+128) else
  if kind == "frame" then
    let ranges := min capacity (inputSize/2+1)
    staticSize*(1+3*(128+16*ranges)+30*ranges+128)
  else if kind == "tp" then
    let parameters := min capacity (inputSize/2)
    staticSize*(1+3*512+20*(parameters+1)^2)
  else if kind.endsWith "-batch" then
    let rounds := min capacity inputSize
    let ranges := if kind == "packet-batch" then 0 else option
    staticSize*(1+3*workCap+rounds*(1+3*(128+16*ranges)+30*ranges+128))
  else staticSize*(1+workCap+3*outputCap+20*(inputSize/16+1)+128)

def frameDescriptorBytes (ranges : Nat) : Nat := 128+16*ranges
def batchSlotBytes (packets : Bool) (ackCapacity : Nat) : Nat :=
  if packets then 144 else 144+16*ackCapacity
def batchOutputBytes (packets : Bool) (ackCapacity capacity : Nat) : Nat :=
  16+batchSlotBytes packets ackCapacity*capacity
def batchWorkBytes (packets : Bool) (ackCapacity capacity : Nat) : Nat :=
  batchOutputBytes packets ackCapacity capacity + batchSlotBytes packets ackCapacity-16

end Libp2pAsm.Asm.Quic.Wire
