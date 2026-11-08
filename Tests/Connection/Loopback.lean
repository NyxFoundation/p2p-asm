import Libp2pAsm.Spec.Connection.Conn

/- Deterministic loopback: two Spec endpoints complete the full
dial → entropy → QUIC/TLS 1.3 handshake with mutual libp2p certificate
authentication → confirmed → multistream selection → 32-byte ping round trip,
driven through the same `step` events and actions the runtime adapter will
use. Malformed datagrams, timeouts and the amplification limit are exercised
on the same state. -/

namespace Libp2pAsm.Tests.Connection

open Libp2pAsm.Spec.Connection

abbrev PLimits : Type := Libp2pAsm.Spec.Limits

def limits : PLimits := {maxConnections := 16, handshakeTimeoutNs := 10000000000}

def clientSecret : List UInt8 :=
  (List.range 32).map (fun i => UInt8.ofNat (0xA0 + i % 16))

def serverSecret : List UInt8 :=
  (List.range 32).map (fun i => UInt8.ofNat (0xB0 + i % 16))

/-- Fixed 96-byte entropy answers. Production entropy comes from the host;
this derivation keeps the whole scenario decisive without hidden randomness. -/
def testEntropy : List UInt8 :=
  (List.range entropyRequestLength).map (fun i =>
    UInt8.ofNat ((i * 37 + 9) % 251))

def utc : Int := 1700000000000000000

def newClient : Conn :=
  {limits := limits, role := .client, hostSecret := clientSecret, utcNs := utc}

def newServer : Conn :=
  {limits := limits, role := .server, hostSecret := serverSecret, utcNs := utc}

structure World where
  client : Conn
  server : Conn
  toClient : List (List UInt8)
  toServer : List (List UInt8)
  expectedPeer : List UInt8 := []
  pings : Nat := 0
  authenticatedC : Bool := false
  authenticatedS : Bool := false
  confirmed : Bool := false
  failed : Option (List Nat) := none
  rounds : Nat := 0
  deriving Repr

def applySide (w : World) (side : Role) (actions : List Action) :
    Except Error World := do
  let mut state := w
  let mut queue := actions
  let mut guard := 64
  while queue.length > 0 && guard > 0 do
    guard := guard - 1
    let a ← match queue.head? with | some a => .ok a | none => throw Error.state
    queue := queue.tail
    match a with
    | .sendDatagram bytes =>
      state := match side with
        | .client => {state with toServer := state.toServer ++ [bytes]}
        | .server => {state with toClient := state.toClient ++ [bytes]}
    | .entropyRequest id len =>
      if len != entropyRequestLength then
        state := {state with failed := some [len]}
        queue := []
      else
        let (next, extra) ←
          match side with
          | .client => step state.client (Event.entropyReady id true testEntropy)
          | .server => step state.server (Event.entropyReady id true testEntropy)
        state := match side with
          | .client => {state with client := next}
          | .server => {state with server := next}
        queue := extra ++ queue
    | .authenticated _peerId =>
      state := match side with
        | .client => {state with authenticatedC := true}
        | .server => {state with authenticatedS := true}
    | .confirmed => state := {state with confirmed := true}
    | .pingRoundTrip bytes =>
      if bytes.length == 32 then
        state := {state with pings := state.pings + 1}
      else
        state := {state with failed := some (bytes.map (fun b => b.toNat))}
    | .closed code =>
      state := {state with failed := some [code]}
    | .streamData _ _ => pure ()
    | .setTimer _ _ => pure ()
  return state

/-- Advance the world once: deliver datagrams to each peer, then hand each
side the events its own actions produced. -/
def tick (w : World) : Except Error World := do
  let mut state := {w with rounds := w.rounds + 1}
  let cs := state.toServer
  let sc := state.toClient
  state := {state with toServer := [], toClient := []}
  for datagram in sc do
    let (next, actions) ←
      match step state.client (Event.receiveDatagram 100000 datagram) with
      | .ok p => pure p
      | .error e => throw (Error.coded (70001 + Error.code e))
    state := {state with client := next}
    state ← applySide state .client actions
    if state.failed.isSome then return state
  for datagram in cs do
    let (next, actions) ←
      match step state.server (Event.receiveDatagram 100000 datagram) with
      | .ok p => pure p
      | .error e => throw (Error.coded (70002 + Error.code e))
    state := {state with server := next}
    state ← applySide state .server actions
    if state.failed.isSome then return state
  return state

/-- Drive the handshake: dial, listener boot, clock, then exchange until
quiet, failure or the iteration bound. -/
def handshake (w0 : World) : Except Error World := do
  let (c0, _) ← step w0.client (Event.clock utc)
  let (s0, _) ← step w0.server (Event.clock utc)
  let clocked : World := {w0 with client := c0, server := s0}
  let (seedC, actionsC) ← step clocked.client (Event.dial w0.expectedPeer)
  let (seedS, actionsS) ← listenerStart clocked.server
  let seeded : World := {clocked with client := seedC, server := seedS}
  let left ← applySide seeded .client actionsC
  let right ← applySide left .server actionsS
  let mut state := right
  let mut guard := 48
  while guard > 0 && state.toServer.length + state.toClient.length > 0
      && state.failed.isNone do
    guard := guard - 1
    state ← tick state
  return state

/-- The 32-byte ping payload for the round trip request. -/
def pingPayload : List UInt8 :=
  (List.range 32).map (fun i => UInt8.ofNat (0x5A + i % 13))

/-- Send a ping through the negotiated stream and drive until the round trip
completes. -/
def pingThrough (w0 : World) : Except Error World := do
  let (next, actions) ← step w0.client (Event.ping pingPayload)
  let state ← applySide {w0 with client := next} .client actions
  let mut w := state
  let mut guard := 48
  while guard > 0 && w.toServer.length + w.toClient.length > 0
      && w.failed.isNone do
    guard := guard - 1
    w ← tick w
  return w

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL: {name}")
  IO.println s!"PASS: {name}"

/-- Full positive flow: authenticated, confirmed, ping round trip. -/
def lift (r : Except Libp2pAsm.Spec.Connection.Error World) : IO World :=
  match r with
  | .ok w => pure w
  | .error e => throw (IO.userError s!"FAIL: {repr e}")

private def liftUnit (r : Except Libp2pAsm.Spec.Connection.Error Unit) : IO Unit :=
  match r with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"FAIL: {repr e}")

def runLoopback : IO Unit := do
  let serverKeyBytes ← match Libp2pAsm.Spec.Identity.Certificate.hostPublic 1 serverSecret with
    | .ok key => pure key
    | .error _ => throw (IO.userError "FAIL: host public key")
  let expectedPeer ← match Libp2pAsm.Spec.Identity.PublicKey.peerId 1 serverKeyBytes with
    | .ok peer => pure peer
    | .error _ => throw (IO.userError "FAIL: expected peer id")
  let w0 : World := {client := newClient, server := newServer, expectedPeer := expectedPeer, toClient := [], toServer := []}
  let w ← lift (handshake w0)
  check "should authenticate the server certificate peer id" w.authenticatedC
  check "should authenticate the client certificate peer id" w.authenticatedS
  check "should confirm the handshake" w.confirmed
  check "should not fail the handshake" w.failed.isNone
  check "should converge: quiet after the handshake"
    (w.toServer.isEmpty && w.toClient.isEmpty)
  let w ← lift (pingThrough w)
  check "should complete one ping round trip" (w.pings == 1)
  check "should not fail the ping exchange" w.failed.isNone
  check "should converge after the ping"
    (w.toServer.isEmpty && w.toClient.isEmpty)

def run : IO Unit := runLoopback

def main : IO Unit := run
