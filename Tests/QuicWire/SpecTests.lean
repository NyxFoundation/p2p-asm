import Libp2pAsm.Spec.Quic.Wire.Packet
import Libp2pAsm.Spec.Quic.Wire.Frame
import Libp2pAsm.Spec.Quic.Wire.Transport

open Libp2pAsm.Spec.Quic.Wire

example : (parsePacket #[0xc0,0,0,0,1,0,0,0,1,0] 0).isOk = true := by decide
example : (parsePacket #[0xc0,0,0,0,1,0,0,0,0] 0).isOk = false := by decide
example : (parseFrame #[0x40,0x01] 2).isOk = true := by decide
example : (parseFrame #[0x1f] 2).isOk = false := by decide
example : (parseTransport #[0x20,0,0x20,0] false 4).isOk = false := by decide
example : (parseTransport #[3,2,0x44,0xb0] false 4).isOk = true := by decide
