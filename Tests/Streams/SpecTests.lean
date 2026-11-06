import Libp2pAsm.Spec.Stream.Receive
import Libp2pAsm.Spec.Stream.Send
import Libp2pAsm.Spec.Multistream.Negotiation
import Libp2pAsm.Spec.Ping.Protocol

namespace Libp2pAsm.Tests.Streams.SpecTests
open Libp2pAsm.Spec

private def check (msg : String) (value : Bool) : IO Unit :=
  unless value do throw (IO.userError msg)

private def errorIs [DecidableEq ε] (r : Except ε α) (e : ε) : Bool :=
  match r with | .error found => decide (found = e) | .ok _ => false

private def receive : IO Unit := do
  let s : Stream.Receive := {capacity := 8}
  let .ok (s,d) := s.put 3 [4,5,6] .data | throw (IO.userError "spec receive")
  check "highest offset credit" (s.highest == 6 && d == 6)
  let .ok (s,d) := s.put 0 [1,2,3] .data | throw (IO.userError "spec gap")
  check "gap adds no credit" (d == 0)
  check "overlap conflict" (errorIs (s.put 2 [9] .data) .conflict)
  let .ok s := s.consume 4 | throw (IO.userError "spec consume")
  check "suffix retained" (s.bytes == [(4,5),(5,6)])
  let .ok (s,d) := s.put 9 [] .reset | throw (IO.userError "spec reset")
  check "reset charges remaining" (d == 3 && s.bytes.isEmpty && s.finalSize == some 9)
  check "inconsistent final" (errorIs (s.put 8 [] .fin) .finalSize)

private def send : IO Unit := do
  let s : Stream.Send := {capacity := 8}
  let .ok s := s.append [1,2,3,4] true | throw (IO.userError "spec append")
  let .ok (p,d) := s.reserve ⟨0,4,true⟩ | throw (IO.userError "spec reserve")
  check "reserve does not send" (d == 4 && p.sent == 0)
  let .ok (c,d) := p.settle false | throw (IO.userError "spec cancel")
  check "cancel releases" (d == 4 && c.sent == 0 && c.pending.isNone)
  let .ok (s,_) := p.settle true | throw (IO.userError "spec sent")
  let .ok s := s.acknowledge ⟨2,2,true⟩ | throw (IO.userError "spec suffix ack")
  check "suffix ack retains prefix" (s.base == 0 && s.data.length == 4)
  let .ok s := s.acknowledge ⟨0,2,false⟩ | throw (IO.userError "spec prefix ack")
  check "whole ack collects" (s.base == 4 && s.data.isEmpty && s.finAck)

private def negotiation : IO Unit := do
  let s : Multistream.State := {role := .listener, proposalLimit := 8, byteLimit := 1024, deadline := 100}
  let wire := Multistream.frame Multistream.header
  for split in List.range (wire.length+1) do
    let .ok r := Multistream.feed s (wire.take split) 0 | throw (IO.userError "spec fragment")
    let .ok r := Multistream.feed r.state (wire.drop split) 0 | throw (IO.userError "spec suffix")
    check "header selection" (r.state.phase == .proposal)
  let .ok r := Multistream.feed s (wire ++ Multistream.frame Multistream.ping ++ [99]) 0
    | throw (IO.userError "spec coalescing")
  check "header leaves choice" (r.consumed == wire.length)
  let .ok r := Multistream.feed r.state (Multistream.frame Multistream.ping ++ [99]) 0
    | throw (IO.userError "spec choice")
  check "choice leaves Ping" (r.selected && r.consumed == 18)
  check "strict UTF8 prefix" (errorIs (Multistream.feed {s with phase := .proposal} [4,224,128] 0) .framing)

private def ping : IO Unit := do
  let payload := (List.range 32).map Nat.toUInt8
  let s : Ping.State := {
    outbound := true, deadline := 100, entropyToken := 1,
    authenticated := true, handshakeConfirmed := true}
  let .ok s := Ping.begin s payload 1 0 | throw (IO.userError "spec entropy")
  for split in List.range 32 do
    let .ok r := Ping.feed s (payload.take split) 0 false | throw (IO.userError "spec ping prefix")
    check "no early match" (!r.matched)
    let .ok r := Ping.feed r.state (payload.drop split) 0 false | throw (IO.userError "spec ping suffix")
    check "matched exact32" (r.matched)
  check "authentication gate" (errorIs (Ping.feed {s with authenticated := false} payload 0 false) .gate)

def run : IO Unit := do
  receive; send; negotiation; ping
  IO.println "PASS independent pure Lean specs"
end Libp2pAsm.Tests.Streams.SpecTests
