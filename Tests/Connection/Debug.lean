import Libp2pAsm.Spec.Connection.Conn
import Tests.Connection.Loopback

open Libp2pAsm.Spec.Connection
open Libp2pAsm.Tests.Connection

private def liftAny (r : Except Libp2pAsm.Spec.Connection.Error (Conn × List Action)) :
    IO (Conn × List Action) :=
  match r with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"FAIL step {Libp2pAsm.Spec.Connection.Error.code e}")

def probe : IO Unit := do
  let serverKeyBytes ←
    match Libp2pAsm.Spec.Identity.Certificate.hostPublic 1 serverSecret with
    | .ok key => pure key
    | .error _ => throw (IO.userError "FAIL key")
  let peer ←
    match Libp2pAsm.Spec.Identity.PublicKey.peerId 1 serverKeyBytes with
    | .ok p => pure p
    | .error _ => throw (IO.userError "FAIL peer")
  let w0 : World := {client := newClient, server := newServer, expectedPeer := peer, toClient := [], toServer := []}
  let (c0, _) ← liftAny (step w0.client (Event.clock utc))
  let (s0, _) ← liftAny (step w0.server (Event.clock utc))
  let (seedC, actionsC) ← liftAny (step c0 (Event.dial peer))
  let (seedS, actionsS) ← liftAny (listenerStart s0)
  let w : World := {w0 with client := seedC, server := seedS}
  let w1 ← lift (applySide w .client actionsC)
  let w2 ← lift (applySide w1 .server actionsS)
  let mut state := w2
  let mut guard := 24
  let mut lastSide := "none"
  while guard > 0 && state.toServer.length + state.toClient.length > 0
      && state.failed.isNone do
    guard := guard - 1
    let ticked ←
      match tick state with
      | .ok v =>
        IO.println s!"tick ok toC {v.toClient.length} toS {v.toServer.length} authC {v.authenticatedC} authS {v.authenticatedS} confirmed {v.confirmed} svTrs {v.server.tls.transcript.length} svPeer {(v.server.tls.peerCertificate).isSome} svReadyInit {(v.server.inInitial).ready.length} svNextInit {(v.server.inInitial).next}"
        pure v
      | .error e =>
        IO.println s!"tick err {repr e} toC {state.toClient.length} toS {state.toServer.length}"
        throw (IO.userError s!"tick err2")
    state := ticked
    IO.println s!"tick: toC {state.toClient.length} toS {state.toServer.length} authC {state.authenticatedC} authS {state.authenticatedS} confirmed {state.confirmed} failed {state.failed.isSome}"
  IO.println s!"end: authC {state.authenticatedC} authS {state.authenticatedS} confirmed {state.confirmed} queues {state.toClient.length}/{state.toServer.length}"
  IO.println s!"client hs digest {(state.client.tls.helloDigest).length} shared {(state.client.tls.shared).length} hsKey {(state.client.spaces.handshake.key).isSome}"
  IO.println s!"server hs digest {(state.server.tls.helloDigest).length} shared {(state.server.tls.shared).length} hsKey {(state.server.spaces.handshake.key).isSome} peerCert {(state.server.tls.peerCertificate).isSome}"
  if state.failed.isSome then
    IO.println s!"failure {state.failed}"

def main : IO Unit := probe
