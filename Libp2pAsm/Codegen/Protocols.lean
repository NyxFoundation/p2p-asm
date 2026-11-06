import Libp2pAsm.Asm.Identity.X509.Certificate
import Libp2pAsm.Asm.Tls.Codec
import Libp2pAsm.Asm.Tls.Encode
import Libp2pAsm.Asm.Tls.Schedule
import Libp2pAsm.Asm.Quic.Wire
import Libp2pAsm.Asm.Stream.Receive
import Libp2pAsm.Asm.Stream.Send
import Libp2pAsm.Asm.Stream.Id
import Libp2pAsm.Asm.Multistream.Negotiation
import Libp2pAsm.Asm.Ping.Protocol

namespace Libp2pAsm.Codegen

def protocolNames : List String :=
  ["x509-parse", "x509-signature-algorithm", "x509-key-algorithm", "time-validity",
   "tls-decode", "tls-encode", "tls-vector", "tls-admit", "tls-handshake-keys",
   "tls-application-keys", "tls-finished", "tls-hash", "tls-message-hash",
   "quic-packet-parse", "quic-frame-parse", "quic-transport-parse",
   "quic-packet-encode", "quic-frame-encode", "quic-transport-encode",
   "quic-packet-batch", "quic-frame-batch", "quic-frame-permission",
   "stream-id", "stream-ordinal", "stream-receive", "stream-consume", "stream-peek",
   "stream-append", "stream-reserve", "stream-settle", "stream-ack", "stream-stop",
   "multistream-feed", "multistream-emit", "multistream-timer", "ping-begin",
   "ping-feed", "ping-release", "ping-finish", "ping-cancel", "ping-timeout", "ping-quota"]

private def streams (name : String) : Option (Except String Rv64.SAsm.Stmt) :=
  match name with
  | "stream-id" => some (.ok Asm.Stream.validateId)
  | "stream-ordinal" => some (.ok Asm.Stream.ordinal)
  | "stream-receive" => some (.ok Asm.Stream.receive)
  | "stream-consume" => some (.ok Asm.Stream.consume)
  | "stream-peek" => some (.ok Asm.Stream.peek)
  | "stream-append" => some (.ok Asm.Stream.append)
  | "stream-reserve" => some (.ok Asm.Stream.reserve)
  | "stream-settle" => some (.ok Asm.Stream.settle)
  | "stream-ack" => some (.ok Asm.Stream.acknowledge)
  | "stream-stop" => some (.ok Asm.Stream.stop)
  | "multistream-feed" => some Asm.Multistream.feed
  | "multistream-emit" => some (.ok Asm.Multistream.emit)
  | "multistream-timer" => some (.ok Asm.Multistream.timer)
  | "ping-begin" => some (.ok Asm.Ping.begin)
  | "ping-feed" => some (.ok Asm.Ping.feed)
  | "ping-release" => some (.ok Asm.Ping.release)
  | "ping-finish" => some (.ok Asm.Ping.finish)
  | "ping-cancel" => some (.ok (Asm.Ping.cancel false))
  | "ping-timeout" => some (.ok (Asm.Ping.cancel true))
  | "ping-quota" => some (.ok Asm.Ping.quota)
  | _ => none

/-- Public code emission, not a networking or authentication wrapper. -/
def protocolRoutine (name : String) : Option (Except String Rv64.SAsm.Stmt) :=
  match name with
  | "x509-parse" => some Asm.Identity.X509.certificate
  | "x509-signature-algorithm" => some (.ok Asm.Identity.X509.Algorithm.signature)
  | "x509-key-algorithm" => some (.ok Asm.Identity.X509.Algorithm.publicKey)
  | "time-validity" => some (.ok Asm.Identity.Time.validity)
  | "tls-decode" => some Asm.Tls.Codec.decode
  | "tls-encode" => some Asm.Tls.Encode.encode
  | "tls-vector" => some (.ok Asm.Tls.Encode.vector)
  | "tls-admit" => some (.ok Asm.Tls.Codec.admitQuic)
  | "tls-handshake-keys" => some (Asm.Tls.Schedule.derive .handshake)
  | "tls-application-keys" => some (Asm.Tls.Schedule.derive .application)
  | "tls-finished" => some (Asm.Tls.Schedule.derive .finished)
  | "tls-hash" => some (Asm.Tls.Schedule.derive .hash)
  | "tls-message-hash" => some (Asm.Tls.Schedule.derive .messageHash)
  | "quic-packet-parse" => some Asm.Quic.Wire.packetParse
  | "quic-frame-parse" => some Asm.Quic.Wire.frameParse
  | "quic-transport-parse" => some Asm.Quic.Wire.transportParse
  | "quic-packet-encode" => some Asm.Quic.Wire.packetEncode
  | "quic-frame-encode" => some Asm.Quic.Wire.frameEncode
  | "quic-transport-encode" => some Asm.Quic.Wire.transportEncode
  | "quic-packet-batch" => some (Asm.Quic.Wire.batchParse true)
  | "quic-frame-batch" => some (Asm.Quic.Wire.batchParse false)
  | "quic-frame-permission" => some Asm.Quic.Wire.framePermission
  | _ => streams name

end Libp2pAsm.Codegen
