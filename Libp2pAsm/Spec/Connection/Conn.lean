import Libp2pAsm.Spec.Connection.Tls
import Libp2pAsm.Spec.Stream.Delivery
import Libp2pAsm.Spec.Multistream.Negotiation
import Libp2pAsm.Spec.Multistream.Lifecycle
import Libp2pAsm.Spec.Ping.Protocol
import Libp2pAsm.Spec.Ping.Lifecycle
import Libp2pAsm.Spec.Codec.QuicVarint
import Libp2pAsm.Spec.Quic.Wire.Batch
import Libp2pAsm.Spec.Identity.Certificate.Issue

/-! Connection core, spec layer: one connection's event-driven step.

State is owned by a single caller (one event loop per design §5). `step`
processes exactly one event into bounded actions plus datagrams it wants to
send. It never blocks, makes no host calls, and returns errors as values.
Resource admission, quotas and instruction accounting belong to the kernel
resource routines; this module carries the protocol state only. -/

namespace Libp2pAsm.Spec.Connection

/-- Timer identifiers used by this core. -/
def timerIdle : Nat := 0
def timerHandshake : Nat := 1
def timerLoss : Nat := 2

inductive Event where
  /-- The adapter supplies the peer identity expectation. -/
  | dial (peerId : List UInt8)
  | clock (wallNs : Int)
  | receiveDatagram (now : Nat) (bytes : List UInt8)
  | entropyReady (requestId : Nat) (ok : Bool) (bytes : List UInt8)
  | sendResult (token outcome : Nat)
  | timerExpired (id now : Nat)
  | ping (bytes : List UInt8)
  | close
  deriving Repr, BEq, DecidableEq

inductive Action where
  | sendDatagram (bytes : List UInt8)
  | entropyRequest (requestId length : Nat)
  | setTimer (id delayNs : Nat)
  | streamData (streamId : Nat) (bytes : List UInt8)
  | pingRoundTrip (bytes : List UInt8)
  | authenticated (peerId : List UInt8)
  | confirmed
  | closed (errorCode : Nat)
  deriving Repr, BEq, DecidableEq

structure StreamEntry where
  id : Nat
  weOpened : Bool
  send : Spec.Stream.Send
  receive : Spec.Stream.Receive
  multistream : Option Spec.Multistream.State := none
  ping : Option Spec.Ping.State := none
  closed : Bool := false
  deriving Repr, BEq

def newStream (id : Nat) (weOpened : Bool) (l : Limits) : StreamEntry where
  id := id
  weOpened := weOpened
  send := {capacity := l.streamSendBytes}
  receive := {capacity := l.streamReceiveBytes}

/-- Packet-number spaces of one connection. -/
structure Spaces where
  initial : Space := {}
  handshake : Space := {}
  application : Space := {}
  deriving Repr, BEq

structure Conn where
  limits : Limits
  role : Role
  hostSecret : List UInt8 := []
  hostKind : Nat := 1
  entropy : List UInt8 := []
  entropyOutstanding : Bool := false
  entropyRequestId : Nat := 0
  expectedPeer : List UInt8 := []
  utcNs : Int := 0
  dcid : List UInt8 := []       -- CID we address the peer with
  scid : List UInt8 := []       -- CID the peer addresses us with
  keyDcid : List UInt8 := []    -- CID that selects the initial keys
  firstDcid : List UInt8 := []  -- the client's first Initial dcid (Retry key)
  retryToken : List UInt8 := []
  authenticated : Bool := false
  confirmed : Bool := false
  peerValidated : Bool := false
  unvalidatedRx : Nat := 0
  unvalidatedTx : Nat := 0
  closedAt : Option Nat := none
  errorCode : Option Nat := none
  now : Nat := 0
  idleDeadline : Nat := 0
  handshakeDeadline : Nat := 0
  lossAt : Nat := 0
  lossCount : Nat := 0
  tls : Tls := {}
  spaces : Spaces := {}
  inInitial : CryptoIn := {}
  inHandshake : CryptoIn := {}
  inApplication : CryptoIn := {}
  outInitial : CryptoOut := {}
  outHandshake : CryptoOut := {}
  outApplication : CryptoOut := {}
  logInitial : List UInt8 := []
  logHandshake : List UInt8 := []
  logApplication : List UInt8 := []
  streams : List StreamEntry := []
  sendToken : Nat := 0
  sendAttempts : Nat := 0
  pendingSends : List (Nat × List UInt8) := []
  pathResponse : Option (List UInt8) := none
  doneSent : Bool := false
  deriving Repr

def inOf (c : Conn) (level : Level) : CryptoIn :=
  match level with
  | .initial => c.inInitial
  | .handshake => c.inHandshake
  | .application => c.inApplication

def setInOf (c : Conn) (level : Level) (v : CryptoIn) : Conn :=
  match level with
  | .initial => {c with inInitial := v}
  | .handshake => {c with inHandshake := v}
  | .application => {c with inApplication := v}

def outOf (c : Conn) (level : Level) : CryptoOut :=
  match level with
  | .initial => c.outInitial
  | .handshake => c.outHandshake
  | .application => c.outApplication

def setOutOf (c : Conn) (level : Level) (v : CryptoOut) : Conn :=
  match level with
  | .initial => {c with outInitial := v}
  | .handshake => {c with outHandshake := v}
  | .application => {c with outApplication := v}

def logOf (c : Conn) (level : Level) : List UInt8 :=
  match level with
  | .initial => c.logInitial
  | .handshake => c.logHandshake
  | .application => c.logApplication

def setLogOf (c : Conn) (level : Level) (v : List UInt8) : Conn :=
  match level with
  | .initial => {c with logInitial := v}
  | .handshake => {c with logHandshake := v}
  | .application => {c with logApplication := v}

def spaceOf (c : Conn) (level : Level) : Space :=
  match level with
  | .initial => c.spaces.initial
  | .handshake => c.spaces.handshake
  | .application => c.spaces.application

def setSpaceOf (c : Conn) (level : Level) (v : Space) : Conn :=
  match level with
  | .initial => {c with spaces := {initial := v, handshake := c.spaces.handshake, application := c.spaces.application}}
  | .handshake => {c with spaces := {initial := c.spaces.initial, handshake := v, application := c.spaces.application}}
  | .application => {c with spaces := {initial := c.spaces.initial, handshake := c.spaces.handshake, application := v}}

def setSpacing (c : Conn) (level : Level) (space : Space) : Conn :=
  setSpaceOf c level space

/-- Numeric level code for diagnostics. -/
def Level.codeOf : Level → Nat
  | .initial => 0
  | .handshake => 1
  | .application => 2

/-- Coalescing order: Initial, then Handshake, then 1-RTT (RFC 9000 §12.2). -/
def levelOrder : List Level := [.initial, .handshake, .application]

/-- 1200-byte padding requirement applies to Initial-bearing datagrams. -/
def padDatagram : Nat := 1200

def entropyRequestLength : Nat := 96

def setClock (c : Conn) (now : Nat) : Conn := {c with now := now}

/-- Derive the 44-byte send/recv key set from a 32-byte traffic secret. -/
def deriveKeys (secret : List UInt8) : Except Error (List UInt8) :=
  match Crypto.Quic.packetKeys secret with
  | .ok keys => if keys.length == 44 then .ok keys else .error .keys
  | .error _ => .error .keys

/-- Install initial keys both directions from the CID that selects them. -/
def armClientInitial (c : Conn) : Except Error Conn :=
  match Crypto.Quic.initial c.dcid with
  | .ok words =>
    if words.length != 184 then .error .keys
    else
      let space : Space := {
        key := (words.drop 96).take 44
        peerKey := (words.drop 140).take 44
        peerSecret := (words.drop 64).take 32
      }
      let conn : Conn := {
        c with
        keyDcid := c.dcid
        spaces := {
          initial := space
          handshake := c.spaces.handshake
          application := c.spaces.application
        }
      }
      .ok conn
  | .error _ => .error .keys

def armServerInitial (c : Conn) (keyDcid : List UInt8) : Except Error Conn :=
  match Crypto.Quic.initial keyDcid with
  | .ok words =>
    if words.length != 184 then .error .keys
    else
      let space : Space := {
        key := (words.drop 140).take 44
        peerKey := (words.drop 96).take 44
        peerSecret := (words.drop 32).take 32
      }
      let conn : Conn := {
        c with
        keyDcid := keyDcid
        spaces := {
          initial := space
          handshake := c.spaces.handshake
          application := c.spaces.application
        }
      }
      .ok conn
  | .error _ => .error .keys

/-- Install handshake and application keys from the TLS schedule. -/
def armHandshake (c : Conn) : Except Error Conn := do
  let some hs := c.tls.handshake | throw .keys
  let sendSecret := (if c.role == .client then hs.client else hs.server).toList
  let recvSecret := (if c.role == .client then hs.server else hs.client).toList
  let sendKey ← deriveKeys sendSecret
  let recvKey ← deriveKeys recvSecret
  let space : Space := {
    c.spaces.handshake with
    key := sendKey
    peerKey := recvKey
    peerSecret := recvSecret
  }
  let conn : Conn := {
    c with
    spaces := {
      initial := c.spaces.initial
      handshake := space
      application := c.spaces.application
    }
  }
  return conn

def armApplication (c : Conn) : Except Error Conn := do
  let some cApp := c.tls.clientApp | throw .keys
  let some sApp := c.tls.serverApp | throw .keys
  let sendSecret := (if c.role == .client then cApp else sApp)
  let recvSecret := (if c.role == .client then sApp else cApp)
  let sendKey ← deriveKeys sendSecret
  let recvKey ← deriveKeys recvSecret
  let space : Space := {
    c.spaces.application with
    key := sendKey
    peerKey := recvKey
    peerSecret := recvSecret
  }
  let conn : Conn := {
    c with
    spaces := {
      initial := c.spaces.initial
      handshake := c.spaces.handshake
      application := space
    }
  }
  return conn

/-- Reassemble one incoming key-phase update: `update` emits next secret
(32) || key (16) || IV (12) with the HP key intentionally unchanged, so the
new 44-byte set reuses the previous HP bytes. -/
def rekeyRecv (s : Space) : Except Error Space := do
  let some secret := s.peerSecret | throw .keys
  let some hpOld := s.peerKey.map (fun k => k.drop 28 |>.take 16) | throw .keys
  if s.recvUpdated then throw .keys
  match Crypto.Quic.update secret with
  | .ok words =>
    if words.length != 60 then .error .keys
    else
      let key := (words.drop 32).take 16 ++ (words.drop 48).take 12 ++ hpOld
      let nextSpace : Space := {
        s with
        recvUpdated := true
        prevRecvKey := s.peerKey
        peerKey := key
        peerSecret := words.take 32
        recvPhase := !s.recvPhase
      }
      .ok nextSpace
  | .error _ => .error .keys

private def insertSortedDesc (n : Nat) (acc : List Nat) : List Nat :=
  match acc with
  | [] => [n]
  | m :: rest => if n == m then acc else if n > m then n :: acc else m :: insertSortedDesc n rest

private def mergeDesc : List Nat → List (Nat × Nat)
  | [] => []
  | n :: rest =>
    match mergeDesc rest with
    | (s,c) :: acc => if s == n+1 then (n, c+1) :: acc else (n,1) :: acc
    | [] => [(n,1)]

/-- ACK frame content: descending merged ranges of the received window. -/
def ackRanges (s : Space) (limit : Nat) : List (Nat × Nat) :=
  (mergeDesc s.seen).take limit

/-- Bounded received-number window: newest entries win, the oldest retire. -/
def recordReceived (window : Nat) (seen : List Nat) (n : Nat) : List Nat :=
  if seen.length < window then n :: seen
  else seen.take (window-1) ++ [n]

def recordPn (s : Space) (n : Nat) (window : Nat) : Space :=
  if s.seen.contains n then s
  else
    let seen := recordReceived window s.seen n
    {
      s with
      seen := seen
      seenNext := max s.seenNext (n+1)
      ackPending := true
    }

def largestSeen (s : Space) : Nat := s.seen.foldl max 0

theorem recordPn_no_duplicate_growth (s : Space) (n window : Nat)
    (h : s.seen.contains n) : (recordPn s n window).seen.length = s.seen.length := by
  unfold recordPn
  rw [if_pos h]

/-- Choose the packet-number encoding width for a fresh packet. -/
def pnWidth (s : Space) : Nat :=
  let gap := s.next - s.acked + 1
  if gap < 128 then 1 else if gap < 32768 then 2 else 4

/-- One assembled, still-plaintext packet awaiting protection. -/
structure Draft where
  level : Level
  plain : List UInt8 := []
  pnOffset : Nat := 0
  number : Nat := 0
  crypto : List (Nat × Nat) := []
  streams : List (Nat × Nat × Nat × Bool) := []
  ackIncluded : Bool := false
  padTo : Nat := 0
  deriving Repr, Inhabited

/-- AEAD tag placeholder counted in the QUIC length field before protection. -/
def tagPlaceholder : List UInt8 := List.replicate 16 0

private def frameInt (n : Nat) : Except Error (List UInt8) :=
  match Spec.Codec.QuicVarint.encode n with
  | .ok bytes => .ok bytes
  | .error _ => .error .malformed

private def cryptoFrame (offset : Nat) (data : List UInt8) :
    Except Error (List UInt8) := do
  let head ← frameInt offset
  let length ← frameInt data.length
  return 6 :: head ++ length ++ data

private def streamFrame (id offset : Nat) (fin : Bool)
    (data : List UInt8) : Except Error (List UInt8) := do
  let sid ← frameInt id
  let off ← frameInt offset
  let length ← frameInt data.length
  let tag := (if fin then 9 else 8) + 4 + 2
  return UInt8.ofNat tag :: sid ++ off ++ length ++ data

private def pingFrame : List UInt8 := [1]

private def doneFrame : List UInt8 := [30]

private def pathResponseFrame (data : List UInt8) : Except Error (List UInt8) := do
  unless data.length == 8 do throw .malformed
  return 27 :: data

private def paddingFrames (n : Nat) : List UInt8 := List.replicate n 0

private def closeFrame (code : Nat) (reason : List UInt8) :
    Except Error (List UInt8) := do
  let e ← frameInt code
  let r ← frameInt reason.length
  return 29 :: e ++ r ++ reason

private def ackFrame (ranges : List (Nat × Nat)) : Except Error (List UInt8) := do
  match ranges with
  | [] => throw .state
  | (start,count) :: rest =>
    let largest := start + count - 1
    let first := largest - start
    let mut bytes ← frameInt largest
    bytes := bytes ++ (← frameInt 0)        -- ack delay 0 (immediate acking)
    bytes := bytes ++ (← frameInt (ranges.length - 1))
    bytes := bytes ++ (← frameInt first)
    let mut low := start
    for (s2,c2) in rest do
      unless s2 < low do throw .state
      bytes := bytes ++ (← frameInt (low - (s2 + c2) - 1))
      bytes := bytes ++ (← frameInt (c2 - 1))
      low := s2
    return 2 :: bytes

/-- Packet-number reconstruction check against the send history: an ACK frame
can only cover packet numbers this endpoint actually produced. -/
def ackWithinHistory (s : Space) (largest : Nat) : Bool := largest < s.next

/-- Encode one packet's plaintext. Shared by protection and the dry-run
length probe that decides exact padding. -/
def encodePlain (c : Conn) (level : Level) (plain : List UInt8) (pnLen : Nat) (truncated : Nat) :
    Except Error (List UInt8) := do
  let kind := if level == .application then Spec.Quic.Wire.PacketKind.short
    else if level == .initial then Spec.Quic.Wire.PacketKind.initial
    else Spec.Quic.Wire.PacketKind.handshake
  let token := if level == .initial && c.role == .client then c.retryToken else []
  match Spec.Quic.Wire.encodePacket
      {kind := kind, dcid := c.dcid, scid := c.scid, token := token,
       payload := plain, pnLength := pnLen,
       truncatedPN := truncated,
       keyPhase := false} maxDatagram with
  | .error _ => .error .limit
  | .ok raw => .ok raw

/-- Wire length of one draft if protected now: header plus pn plus the
plaintext plus the AEAD tag, exactly what the sealed packet occupies. -/
def draftRawLength (c : Conn) (d : Draft) : Except Error Nat := do
  let pnLen := pnWidth (spaceOf c d.level)
  match encodePlain c d.level (d.plain ++ tagPlaceholder) pnLen (d.number % 256^pnLen) with
  | .error _ => throw .limit
  | .ok raw => return raw.length

/-- Protect one draft into final wire bytes. The AEAD-tag placeholder keeps
the QUIC length field equal to pn plus the ciphertext while the real
plaintext rides inside the envelope; `padTo > 0` appends exactly enough
PADDING so the sealed length reaches the target. -/
def protectDraft (c : Conn) (d : Draft) : Except Error (List UInt8 × Draft) := do
  let space := spaceOf c d.level
  match space.key with
  | .none => .error .keys
  | .some key =>
    let pnLen := pnWidth space
    -- A length-field varint that widens as padding crosses a size class would
    -- otherwise overshoot the datagram bound; home in on the exact target with
    -- a bounded fixpoint: pad, re-encode, and stop once the length stops shrinking.
    -- The header-protection mask samples 16 ciphertext bytes, so the sealed span
    -- must fit at least `headerLength + 4` input bytes; pad short ACK-only drafts.
    let plain <-
      if d.padTo == 0 then .ok d.plain
      else
        (List.range 4).foldlM (fun (plainSoFar : List UInt8) (_ : Nat) =>
          match encodePlain c d.level (plainSoFar ++ tagPlaceholder) pnLen
              (d.number % 256^pnLen) with
          | .error _ => throw .limit
          | .ok raw =>
            if raw.length >= d.padTo then .ok plainSoFar
            else .ok (plainSoFar ++ paddingFrames (d.padTo - raw.length)))
          d.plain
    let paddedPlain : List UInt8 :=
      let minPlain := 4 - pnLen
      if plain.length < minPlain then plain ++ paddingFrames (minPlain - plain.length)
      else plain
    match encodePlain c d.level (paddedPlain ++ tagPlaceholder) pnLen (d.number % 256^pnLen) with
    | .error _ => .error .limit
    | .ok raw =>
      let headerLen := raw.length - pnLen - paddedPlain.length - 16
      let head : List UInt8 := raw.extract 0 headerLen
      let pnField : List UInt8 := Spec.Codec.QuicVarint.bigEndian pnLen (d.number % 256^pnLen)
      let input : Array UInt8 := (head ++ pnField ++ paddedPlain).toArray
      match Crypto.Quic.protect key.toArray input headerLen (headerLen + pnLen) d.number maxDatagram with
      | .error _ => .error .keys
      | .ok sealed => .ok (sealed.toList, {d with plain := plain})

/-- One assembled packet plus the stream reservations it carries. -/
structure DraftBundle where
  level : Level
  draft : Draft
  reserved : List (StreamEntry × Spec.Stream.Range)
  deriving Repr, Inhabited

/-- Fill one level's packet body with ACK, CRYPTO and control frames within
`budget` payload bytes; stream frames at the application level only. Stream
reservations are returned unsettled so a failed emission can release them.
Padding (`extra`) is appended after all real frames. -/
def fillDraft (c : Conn) (level : Level) (budget extra : Nat) :
    Except Error (Conn × Draft × List (StreamEntry × Spec.Stream.Range)) := do
  let space := spaceOf c level
  let out := outOf c level
  let mut state := c
  let mut body : List UInt8 := []
  let mut cryptoPieces : List (Nat × Nat) := []
  let mut streamPieces : List (Nat × Nat × Nat × Bool) := []
  let mut reserved : List (StreamEntry × Spec.Stream.Range) := []
  let mut ackIncluded := false
  let mut remaining := budget
  if space.ackPending then
    let ranges := ackRanges space state.limits.maxAckRanges
    match ranges with
    | _ :: _ =>
      let frame ← ackFrame ranges
      if frame.length ≤ remaining then
        body := body ++ frame
        remaining := remaining - frame.length
        ackIncluded := true
    | [] => pure ()
  if level != .application then
    if out.buffer.length > 0 then
      let k := min remaining out.buffer.length
      let piece ← cryptoFrame out.offset (out.buffer.take k)
      if piece.length ≤ remaining then
        body := body ++ piece
        remaining := remaining - piece.length
        cryptoPieces := (out.offset, k) :: cryptoPieces
        let (out', _) := CryptoOut.take out k
        state := setOutOf state level out'
        state := setLogOf state level (logOf state level ++ out.buffer.take k)
  else
    if state.doneSent == false && state.tls.phase == Phase.done
        && state.role == .server then
      if remaining ≥ doneFrame.length then
        body := body ++ doneFrame
        remaining := remaining - doneFrame.length
        state := {state with doneSent := true}
    match state.pathResponse with
    | some data =>
      let frame ← pathResponseFrame data
      if frame.length ≤ remaining then
        body := body ++ frame
        remaining := remaining - frame.length
        state := {state with pathResponse := none}
    | none => pure ()
    for entry in state.streams do
      match entry.send.pending with
      | none =>
        if remaining > 25 then
          let queued := entry.send.queued
          let unsent := if queued > entry.send.sent then queued - entry.send.sent else 0
          if unsent > 0 then
            let budget := min unsent (remaining - 25)
            if budget > 0 then
              let fin := entry.send.finalSize == some (entry.send.sent + budget)
              let reserve : Spec.Stream.Range :=
                {start := entry.send.sent, length := budget, fin := fin}
              match Spec.Stream.Send.reserve entry.send reserve with
              | .ok (send', _) =>
                let bytes := (entry.send.data.drop (reserve.start - entry.send.base)).take budget
                let piece ← streamFrame entry.id reserve.start fin bytes
                if piece.length ≤ remaining then
                  body := body ++ piece
                  remaining := remaining - piece.length
                  streamPieces := streamPieces ++ [(entry.id, reserve.start, budget, fin)]
                  let committed := {entry with send := send'}
                  reserved := reserved ++ [(committed, reserve)]
                  let replaced := state.streams.map (fun e =>
                    if e.id == entry.id then committed else e)
                  state := {state with streams := replaced}
              | .error _ => pure ()
      | some _ => pure ()
  if extra > 0 then
    body := body ++ paddingFrames extra
  let d : Draft := Draft.mk level body 0 0 cryptoPieces streamPieces ackIncluded 0
  pure (state, d, reserved)

/-- Unwind reservations when a round aborts before protection succeeds. -/
def releaseReservations (c : Conn)
    (reserved : List (StreamEntry × Spec.Stream.Range)) : Conn :=
  if reserved.isEmpty then c
  else
    let updated := c.streams.map (fun e =>
      let hits := reserved.filter (fun p => p.1.id == e.id)
      match hits with
      | [] => e
      | _ :: _ =>
        match Spec.Stream.Send.settle e.send false with
        | .ok (send', _) => {e with send := send'}
        | .error _ => e)
    {c with streams := updated}

/-- Commit reservations after a successful send. -/
def settleReservations (c : Conn)
    (reserved : List (StreamEntry × Spec.Stream.Range)) : Except Error Conn := do
  if reserved.isEmpty then return c
  else
    let updated := c.streams.map (fun e =>
      let hits := reserved.filter (fun p => p.1.id == e.id)
      match hits with
      | [] => e
      | _ :: _ =>
        match Spec.Stream.Send.settle e.send true with
        | .ok (send', _) => {e with send := send'}
        | .error _ => e)
    return {c with streams := updated}

/-- Protect a single bundle: fresh packet number from the level space, commit
the reservation and the space bookkeeping. Failure leaves the level space
untouched and the caller releases its reservations. -/
def protectBundle (c : Conn) (b : DraftBundle) :
    Except Error (Conn × List UInt8) := do
  let space := spaceOf c b.level
  let number := space.next
  let (sealedBytes, sealed) ← protectDraft c {b.draft with number := number}
  let committed ← settleReservations c b.reserved
  let space' := spaceOf committed b.level
  let record : SentRecord :=
    {number := number,
      sentAt := committed.now,
      attempts := 1,
      crypto := sealed.crypto,
      streams := sealed.streams}
  let spaceNext : Space := {
    space' with
    next := number + 1
    ackPending := !sealed.ackIncluded && space'.ackPending
    unacked := List.take committed.limits.maxSentPackets (record :: space'.unacked)
  }
  let conn := setSpaceOf committed b.level spaceNext
  let conn := if conn.role == .server && !conn.peerValidated then
    {conn with unvalidatedTx := conn.unvalidatedTx + sealedBytes.length}
  else conn
  return (conn, sealedBytes)

/-- Total budget used by assembled bundles so far. -/
def wireSoFar (bundles : List DraftBundle) : Nat :=
  bundles.foldl (fun acc b => acc + b.draft.plain.length + 40) 0

/-- Does this level still have something to send in a fresh round? -/
def levelPending (c : Conn) (level : Level) : Bool :=
  ((outOf c level).buffer.length > 0 || (spaceOf c level).ackPending) ||
    (level == .application &&
      ((!c.doneSent && c.tls.phase == Phase.done && c.role == .server) ||
       c.pathResponse.isSome ||
       c.streams.any (fun e => !e.closed && e.send.pending.isNone &&
         e.send.queued > e.send.sent)))

/-- Emit one datagram: coalesce at most one packet per level, pad the last
packet of an Initial-bearing datagram to exactly the 1200-byte bound, protect
in order, and stop at the datagram bound. -/
def emitRound (c : Conn) : Except Error (Conn × List Action) := do
  let mut state := c
  let mut bundles : List DraftBundle := []
  let mut hasInitial := false
  for level in levelOrder do
    if levelPending state level && wireSoFar bundles + 40 ≤ maxDatagram then
      let payloadBudget := maxDatagram - wireSoFar bundles - 40
      let (s, d, rs) ← fillDraft state level payloadBudget 0
      if d.plain.isEmpty && !d.ackIncluded then
        state := releaseReservations s rs
      else
        state := s
        bundles := bundles ++ [{level := level, draft := d, reserved := rs}]
        if level == .initial then hasInitial := true
  if bundles.isEmpty then return (state, [])
  let mut wire : List UInt8 := []
  let mut state2 := state
  for idx in List.range bundles.length do
    let b := bundles[idx]!
    let isLast := idx + 1 == bundles.length
    let rawLen ← draftRawLength state2 b.draft
    let padTo := if isLast && hasInitial && wire.length + rawLen < padDatagram
      then padDatagram - wire.length else 0
    let prepared : DraftBundle := {b with draft := {b.draft with padTo := padTo}}
    let sealedLen := if padTo > 0 then padTo else rawLen
    if wire.length + sealedLen ≤ maxDatagram then
      let (s, bytes) ← protectBundle state2 prepared
      state2 := s
      wire := if wire.isEmpty then bytes else wire ++ bytes
    else
      state2 := releaseReservations state2 prepared.reserved
  if wire.isEmpty then return (state2, [])
  return (state2, [Action.sendDatagram wire])

/-- Does the current phase accept TLS bytes at this level? -/
def tlsLevelActive (c : Conn) (level : Level) : Bool :=
  match c.role, c.tls.phase, level with
  | Role.client, Phase.waitSH, Level.initial => true
  | Role.client, Phase.waitFlight, Level.handshake => true
  | Role.server, Phase.fresh, Level.initial => true
  | Role.server, Phase.waitClient, Level.handshake => true
  | _, _, _ => false

/-- Deliver one contiguous crypto chunk to the TLS role of the phase.
Returns the new state when a decode consumed bytes, or `none` when the state
machine needs more data at that level. -/
def feedOnce (c : Conn) (level : Level) :
    Except Error (Option (Conn × Nat)) := do
  let ready := (inOf c level).ready
  match ready with
  | [] => .ok none
  | _ =>
    let result ←
      match c.role, c.tls.phase with
      | Role.client, Phase.waitSH =>
        clientFeed c.tls c.limits level ready
      | Role.client, Phase.waitFlight =>
        clientFeed c.tls c.limits level ready
      | Role.client, _ => .error .state
      | Role.server, Phase.fresh =>
        serverAccept c.tls c.limits level ready
      | Role.server, Phase.waitClient =>
        serverFeed c.tls c.limits level ready
      | Role.server, _ => .error .state
    let (tls, flights, consumed) := result
    if consumed == 0 then
      .ok none
    else
      let mut state := c
      state := {state with tls := tls}
      let dropped ←
        match (inOf state level).dropReady consumed with
        | .ok v2 => .ok v2
        | .error e => .error (.coded (26000 + Error.code e))
      state := setInOf state level dropped
      for f in flights do
        let out := outOf state f.level
        let appended ← out.append f.bytes state.limits.cryptoBufferBytes
        state := setOutOf state f.level appended
      .ok (some (state, consumed))

/-- Feed as many TLS messages as the contiguous crypto bytes allow, at the
levels implied by the phase. Installs handshake/application keys and flips
validation flags when the schedule stages complete. -/
def feedTls (c : Conn) : Except Error (Conn × List Action) := do
  let mut state := c
  let mut progress := true
  while progress do
    progress := false
    let level : Level := match state.role, state.tls.phase with
      | Role.client, Phase.waitSH => Level.initial
      | Role.client, Phase.waitFlight => Level.handshake
      | Role.server, Phase.fresh => Level.initial
      | Role.server, Phase.waitClient => Level.handshake
      | _, _ => Level.application
    if !(tlsLevelActive state level) then
      -- nothing to feed in this phase
      pure ()
    else
      match ← feedOnce state level with
      | none => pure ()
      | some (next, _) =>
        state := next
        progress := true
  -- install keys and side effects after any state change
  let mut actions : List Action := []
  if state.tls.handshake.isSome && state.tls.shared.length > 0 &&
      (state.spaces.handshake.key == none) then
    state := ← armHandshake state
  if state.tls.clientApp.isSome && state.tls.serverApp.isSome &&
      (state.spaces.application.key == none) then
    state := ← armApplication state
  if state.tls.peerId.isSome && !state.authenticated then
    state := {state with authenticated := true}
    match state.tls.peerId with
    | some peerId => actions := actions ++ [Action.authenticated peerId]
    | none => pure ()
  -- server completing the client's Finished validates the peer's address
  if state.role == .server && state.tls.phase == Phase.done && !state.peerValidated then
    -- the server's handshake completes with its own HANDSHAKE_DONE emission
    state := {state with confirmed := true}
    state := {state with peerValidated := true}
  return (state, actions)

/-- Open the ping negotiation stream as the dialer once the handshake is
confirmed. The header is written immediately; the proposal waits for the
listener echo per multistream-select. -/
def openPingStream (c : Conn) : Except Error Conn := do
  if c.streams.any (fun e => e.id == 0) then return c
  let entry : StreamEntry := {
    id := 0
    weOpened := true
    send := {capacity := c.limits.streamSendBytes}
    receive := {capacity := c.limits.streamReceiveBytes}
    multistream := some {
      role := Spec.Multistream.Role.dialer
      proposalLimit := c.limits.maxProposals
      byteLimit := c.limits.maxNegotiationBytes
      deadline := c.now + c.limits.negotiationTimeoutNs
    }
  }
  let header ←
    match Spec.Multistream.encodeFrame Spec.Multistream.header with
    | .ok raw => .ok raw
    | .error _ => .error .malformed
  let send ←
    match entry.send.append header false with
    | .ok s => .ok s
    | .error _ => .error .limit 
  let opened : StreamEntry := {
    entry with
    send := send
  }
  pure {c with streams := opened :: c.streams}

/-- Accept an application-level stream on the listener: bidirectional
client-initiated ids under the stream limit only. -/
def acceptStream (c : Conn) (id : Nat) : Except Error (Conn × StreamEntry) := do
  if c.role != .server then throw .state
  if id % 4 != 0 then throw .unsupported
  if id / 4 ≥ c.limits.maxStreamsPerConnection then throw .limit
  match c.streams.find? (fun e => e.id == id) with
  | some e => .ok (c, e)
  | none =>
    let entry : StreamEntry := {
      id := id
      weOpened := false
      send := {capacity := c.limits.streamSendBytes}
      receive := {capacity := c.limits.streamReceiveBytes}
      multistream := some {
        role := Spec.Multistream.Role.listener
        proposalLimit := c.limits.maxProposals
        byteLimit := c.limits.maxNegotiationBytes
        deadline := c.now + c.limits.negotiationTimeoutNs
      }
    }
    .ok ({c with streams := entry :: c.streams}, entry)

/-- Push received stream bytes through multistream negotiation and ping echo.
Returns the consumed actions (stream data to the application, ping results). -/
def pumpStreams (c : Conn) : Except Error (Conn × List Action) := do
  let mut state := c
  let mut actions : List Action := []
  let mut progress := true
  let mut guard := state.limits.maxStreamsPerConnection * 4 + 8
  while progress && guard > 0 do
    progress := false
    guard := guard - 1
    let mut next : List StreamEntry := []
    let mut replaced := false
    for entry in state.streams do
      if entry.closed then
        next := next ++ [entry]
      else
        let delivery := entry.receive.delivery
        match entry.multistream with
        | some m =>
          if delivery.isEmpty then
            next := next ++ [entry]
          else if entry.ping.isSome && m.phase == Spec.Multistream.Phase.selected then
            let some ping := entry.ping | next := next ++ [entry]
            match
              (Except.mapError (fun _ => Error.coded (18 : Nat))
                (Spec.Ping.feed ping delivery state.now
                  (entry.receive.finalSize == some
                    (entry.receive.consumed + delivery.length)))) with
            | .error e9 =>
              let s := match Spec.Stream.Send.stop entry.send with
                | .ok s => s
                | .error _ => entry.send
              next := next ++ [{entry with closed := true, ping := none, send := s}]
              replaced := true
              progress := true
            | .ok result =>
              let mut entry2 := entry
              match (Except.mapError (fun _ => Error.coded (19501 : Nat))
                (entry2.receive.consume result.consumed)) with
              | .ok r => entry2 := {entry2 with receive := r}
              | .error _ => .error (Error.coded 19502)
              if result.echo.length > 0 then
                let s2 ←
                  match entry2.send.append result.echo true with
                  | .ok s2 => .ok s2
                  | .error _ => .error .limit
                entry2 := {entry2 with send := s2}
              if result.matched then
                actions := actions ++ [Action.pingRoundTrip result.state.expected]
                let released
                  ← match Spec.Ping.release result.state state.now with
                    | .ok rel => .ok rel
                    | .error _ => .ok result.state
                entry2 := {entry2 with ping := some released}
              next := next ++ [entry2]
              replaced := true
              progress := true
          else
            match
              (Except.mapError (fun _ => Error.coded (17 : Nat))
                (Spec.Multistream.feed m delivery state.now)) with
            | .error _ =>
              -- deadline/framing failure closes the stream for both sides
              let send := match Spec.Stream.Send.stop entry.send with
                | .ok s => s
                | .error _ => entry.send
              next := next ++ [{entry with closed := true, multistream := none, send := send}]
              replaced := true
              progress := true
            | .ok result =>
              let mut entry := entry
              let receiveOk ←
                match (Except.mapError (fun _ => Error.coded (19001 : Nat))
                  (entry.receive.consume result.consumed)) with
                | .ok r => .ok r
                | .error _ => .error (Error.coded 19002)
              let receive := receiveOk
              entry := {entry with receive := receive}
              -- this side's own write when it advances a negotiation phase
              let sideWrite : Except Error (List UInt8) :=
                if m.phase == Spec.Multistream.Phase.header &&
                    result.state.phase == Spec.Multistream.Phase.proposal then
                  if entry.weOpened then
                    match Spec.Multistream.encodeFrame Spec.Multistream.ping with
                    | .ok p => .ok p
                    | .error _ => .error .malformed
                  else
                    match Spec.Multistream.encodeFrame Spec.Multistream.header with
                    | .ok h => .ok h
                    | .error _ => .error .malformed
                else .ok []
              let responseSend ←
                match entry.send.append result.response false with
                | .ok s0 => .ok s0
                | .error _ => .error (.coded 20010)
              let sideBytes ← sideWrite
              let send ←
                match responseSend.append sideBytes false with
                | .ok s1 => .ok s1
                | .error _ => .error (.coded 20011)
              entry := {entry with send := send}
              if result.selected then
                if !entry.weOpened && entry.ping.isNone then
                  -- the echo side only; the dialer starts its ping via the ping event
                  let ping : Spec.Ping.State := {
                    outbound := false
                    phase := 0
                    deadline := state.now + state.limits.pingTimeoutNs
                    entropyToken := 0
                    authenticated := state.authenticated
                    handshakeConfirmed := state.confirmed
                  }
                  entry := {entry with ping := some ping}
              entry := {entry with multistream := some result.state}
              next := next ++ [entry]
              replaced := true
              progress := true
        | none =>
          match entry.ping with
          | none => next := next ++ [entry]
          | some ping =>
            if delivery.isEmpty then
              next := next ++ [entry]
            else
              let fin := entry.receive.finalSize == some (entry.receive.consumed + delivery.length)
              match
                (Except.mapError (fun _ => Error.coded (18 : Nat))
                  (Spec.Ping.feed ping delivery state.now fin)) with
              | .error _ =>
                -- timeout/closed ping: cancel and clean the stream
                let send := match Spec.Stream.Send.stop entry.send with
                  | .ok s => s
                  | .error _ => entry.send
                next := next ++ [{entry with closed := true, ping := none, send := send}]
                replaced := true
                progress := true
              | .ok result =>
                let mut entry := entry
                let receiveOk ←
                  match (Except.mapError (fun _ => Error.coded (19501 : Nat))
                    (entry.receive.consume result.consumed)) with
                  | .ok r => .ok r
                  | .error _ => .error (Error.coded 19502)
                let receive := receiveOk
                entry := {entry with receive := receive}
                if result.echo.length > 0 then
                  let send ←
                    match entry.send.append result.echo true with
                    | .ok s2 => .ok s2
                    | .error _ => .error .limit
                  entry := {entry with send := send}
                if result.matched then
                  actions := actions ++ [Action.pingRoundTrip result.state.expected]
                  -- the initiator releases after a matched echo
                  match Spec.Ping.release result.state state.now with
                  | .ok released => entry := {entry with ping := some released}
                  | .error _ => entry := {entry with ping := some result.state}
                let cleaned := entry
                let pingPhase := match cleaned.ping with
                  | some p => p.phase
                  | none => 99
                let finished := receive.eof &&
                  (cleaned.send.finAck || cleaned.send.reset) &&
                  (pingPhase == 3 || (cleaned.send.finSent && !cleaned.send.reset && pingPhase == 2 &&
                    !cleaned.weOpened))
                if finished then
                  replaced := true
                  progress := true
                  next := next ++ [{cleaned with closed := true, ping := none}]
                else
                  next := next ++ [cleaned]
    if replaced then
      state := {state with streams := next}
    else
      progress := false
  return (state, actions)

/-- Run the TLS feed loop and pump the application streams after any crypto
or stream insertion. Consolidates key installation plus action emission. -/
def advance (c : Conn) : Except Error (Conn × List Action) := do
  let (tls, tlsActions) ← feedTls c
  let (pumped, pumpActions) ← pumpStreams tls
  return (pumped, tlsActions ++ pumpActions)

/-- Acknowledge covered packet numbers: drop sent records, acknowledge the
stream ranges they carried, and advance the largest-acked marker. -/
def applyAck (c : Conn) (level : Level) (ranges : List (Nat × Nat)) :
    Except Error Conn := do
  let space := spaceOf c level
  let numbers := ranges.flatMap (fun (start, count) =>
    (List.range count).map (fun i => start + i))
  let covered := space.unacked.filter (fun r => numbers.contains r.number)
  let kept := space.unacked.filter (fun r => !numbers.contains r.number)
  let largest := numbers.foldl (fun acc n => max acc (n+1)) space.acked
  let commits : List (Nat × Spec.Stream.Range) :=
    covered.flatMap (fun r => r.streams.map (fun (id, start, len, fin) =>
      (id, {start := start, length := len, fin := fin})))
  let spaceNext : Space := {
    space with
    unacked := kept
    acked := largest
  }
  let mut state := setSpaceOf c level spaceNext
  for (id, range) in commits do
    let updated := state.streams.map (fun e =>
      match Spec.Stream.Send.acknowledge e.send range with
      | .ok send' => {e with send := send'}
      | .error _ => e)
    state := {state with streams := updated}
  -- An ACK of a handshake or 1-RTT packet we sent confirms the peer's address.
  if state.role == .client && level != .initial && !covered.isEmpty then
    state := {state with peerValidated := true}
  return state

/-- Frame walk tolerant of trailing PADDING: parse frames from the front; when
a parse stops making progress, accept the rest only if it is all zeros.
Zero bytes INSIDE frames (e.g. a zero largest/first-range ACK field) are
protected because the walk consumes whole frames. -/
def parseFramesTolerant (payload : Array UInt8) (ackCapacity frameCapacity : Nat) :
    Except Error (List (Nat × Spec.Quic.Wire.Frame)) := do
  match Spec.Quic.Wire.parseFrames payload ackCapacity frameCapacity with
  | .ok fs => .ok fs
  | .error _ =>
    -- walk frame by frame until an error, then check the tail is padding
    let mut pos := 0
    let mut acc : List (Nat × Spec.Quic.Wire.Frame) := []
    let mut fuel := frameCapacity
    let mut bad := false
    while !bad && fuel > 0 && pos < payload.size do
      fuel := fuel - 1
      match Spec.Quic.Wire.parseFrame (payload.extract pos payload.size) ackCapacity with
      | .ok f =>
        if f.consumed == 0 then bad := true
        else
          acc := (pos, f) :: acc
          pos := pos + f.consumed
      | .error _ => bad := true
    if bad then
      -- accept the remainder as PADDING only when every remaining byte is zero
      let rest := payload.extract pos payload.size
      if rest.all (fun b => b == 0) then .ok acc.reverse
      else .error (.coded (50310 : Nat))
    else .ok acc.reverse

/-- Ack-eliciting decision for a decrypted payload: any frame other than
ACK or PADDING requests an acknowledgment (RFC 9002 6.2.2). -/
def ackEliciting (payload : Array UInt8) : Bool :=
  match parseFramesTolerant payload 64 64 with
  | .error _ => true
  | .ok frames =>
    if frames.isEmpty then false
    else frames.any (fun f =>
      match f.2.body with
      | .ack _ => false
      | .padding => false
      | _ => true)

/-- Process the frames of one decrypted packet. The wire views inside frame
bodies are relative to each frame's own input, so every extraction adds the
frame's position within the decrypted payload. -/
def processFrames (c : Conn) (level : Level) (payload : Array UInt8)
    (now : Nat) : Except Error (Conn × List Action) := do
  let frames ←
    match (parseFramesTolerant payload
        c.limits.maxAckRanges c.limits.maxFramesPerQuantum) with
    | .ok fs => .ok fs
    | .error e2 => .error (.coded (50250 + e2.code % 50))
  let mut state := c
  let mut actions : List Action := []
  for pair in frames do
    let framePos := pair.1
    match pair.2.body with
    | .padding => pure ()
    | .ping => pure ()
    | .crypto streamOffset slice =>
      let data := (payload.extract (framePos + slice.offset) (framePos + slice.offset + slice.length)).toList
      match (inOf state level).insert streamOffset data state.limits.cryptoBufferBytes with
      | .ok inserted => state := setInOf state level inserted
      | .error e2 => throw (Error.coded (47000 + Error.code e2))
    | .ack a =>
      let first : List (Nat × Nat) := [(a.largest - a.firstRange, a.firstRange + 1)]
      let rest := a.ranges.map (fun r => (r.low, r.high - r.low + 1))
      let _ := a.encodedRanges
      if !ackWithinHistory (spaceOf state level) a.largest then throw (.coded (50301 : Nat))
      state := ← applyAck state level (first ++ rest)
    | .stream id offset fin _ _ slice =>
      let data := (payload.extract (framePos + slice.offset) (framePos + slice.offset + slice.length)).toList
      let lookup := state.streams.find? (fun e => e.id == id)
      let next ←
        match lookup with
        | some _ => .ok state
        | none =>
          if level == .application && state.role == .server then
            match acceptStream state id with
            | .ok (opened, _) => .ok opened
            | .error _ => .ok state
          else .ok state
      match next.streams.find? (fun e => e.id == id) with
      | some entry =>
        let kind := if fin then Spec.Stream.ReceiveKind.fin
          else Spec.Stream.ReceiveKind.data
        match entry.receive.put offset data kind with
        | .ok (receive, _) =>
          state := {next with streams := next.streams.map (fun e =>
            if e.id == id then {e with receive := receive} else e)}
        | .error _ => throw (.coded (50302 : Nat))
      | none => pure () -- stream not admissible in this profile: drop
    | .resetStream id _ finalSize =>
      match state.streams.find? (fun e => e.id == id) with
      | some entry =>
        match entry.receive.put finalSize [] Spec.Stream.ReceiveKind.reset with
        | .ok (receive, _) =>
          state := {state with streams := state.streams.map (fun e =>
            if e.id == id then {e with receive := receive} else e)}
        | .error _ => pure () -- a late reset beyond final size is ignored
      | none => pure ()
    | .stopSending id _ =>
      state := {state with streams := state.streams.map (fun e =>
        if e.id == id then
          match Spec.Stream.Send.stop e.send with
          | .ok send' => {e with send := send'}
          | .error _ => e
        else e)}
    | .maxStreamData id value =>
      state := {state with streams := state.streams.map (fun e =>
        if e.id == id then
          {e with send := {e.send with limit := max e.send.limit value}}
        else e)}
    | .maxData _ => pure () -- this profile never blocks on the connection budget
    | .dataBlocked _ => pure ()
    | .pathChallenge slice =>
      let data := payload.extract (framePos + slice.offset) (framePos + slice.offset + slice.length)
      state := {state with pathResponse := some data.toList}
    | .pathResponse _ => pure ()
    | .newToken _ => pure () -- the profile sends no stateless retry
    | .newConnectionId _ _ _ _ => pure () -- single-CID profile, no migration
    | .retireConnectionId _ => pure ()
    | .maxStreams _ _ => pure ()
    | .streamsBlocked _ _ => pure ()
    | .streamDataBlocked _ _ => pure ()
    | .connectionClose _ code _ _ =>
      state := {state with closedAt := some now, errorCode := some (state.errorCode.getD code)}
      actions := actions ++ [Action.closed code]
    | .handshakeDone =>
      if state.role == .client && !state.confirmed then
        state := {state with confirmed := true, peerValidated := true}
        let openedStream ← openPingStream state
        state := openedStream
        actions := actions ++ [Action.confirmed]
  pure (state, actions)

/-- One decrypted packet result: the level, packet number and payload. -/
structure Decrypted where
  level : Level
  number : Nat
  payload : Array UInt8
  deriving Repr, BEq

def shortKeyPhaseBit (first : Nat) : Bool := first / 4 % 2 == 1

def kindLevel (k : Spec.Quic.Wire.PacketKind) : Except Error Level :=
  match k with
  | .initial => .ok .initial
  | .handshake => .ok .handshake
  | .short => .ok .application
  | _ => .error .unsupported

/-- Decrypt one packet with the receive keys selected by the (HP-masked) key
phase bit. A fresh phase forces the single forward key update before
decryption; a stale packet falls back to the previous keys. -/
def decryptPacket (c : Conn) (space : Space) (level : Level)
    (packet : Spec.Quic.Wire.Packet) (bytes : Array UInt8) (pos : Nat) :
    Except Error (Option (Decrypted × Space)) := do
  let phase := if level == .application then shortKeyPhaseBit packet.first else false
  let openable : Except Error (Option Space) :=
    if phase == space.recvPhase then .ok (some space)
    else if phase == !space.recvPhase && !space.recvUpdated then
      match rekeyRecv space with
      | .ok next => .ok (some next)
      | .error _ => .ok none
    else .ok none -- a second update, or a phase beyond this profile
  match openable with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some candidate) =>
    match candidate.peerKey with
    | none => .ok none
    | some key =>
      -- coalescing: the AEAD covers exactly this packet's own length span
      let own : Array UInt8 :=
        bytes.extract pos (min (pos + packet.pnOffset + packet.protectedLength) bytes.size)
      let tryKeys (keys : List UInt8) : Except Error (Option Decrypted) :=
        match Crypto.Quic.unprotect keys.toArray own packet.pnOffset candidate.seenNext maxDatagram with
        | .error _ => .ok none
        | .ok opened =>
          .ok (some (Decrypted.mk level opened.number
            (opened.packet.extract opened.headerLength opened.packet.size)))
      match tryKeys key with
      | .ok (some result) => .ok (some (result, candidate))
      | _ =>
        match candidate.prevRecvKey with
        | some prev =>
          match tryKeys prev with
          | .ok (some result) => .ok (some (result, candidate))
          | _ => .ok none
        | none => .ok none

/-- Handle one packet of a received datagram. -/
def onPacket (c : Conn) (packet : Spec.Quic.Wire.Packet)
    (bytes : Array UInt8) (pos : Nat) (now : Nat) :
    Except Error (Conn × List Action) := do
  if c.closedAt.isSome then return (c, [])
  match packet.kind with
  | .versionNegotiation =>
    -- The profile speaks only version 1: a VN that lists 1 is malformed, any
    -- other VN means the peer cannot interoperate.
    let listed := (bytes.extract packet.tail.offset (packet.tail.offset + packet.tail.length)).toList
    let hasOne := (List.range (listed.length / 4)).any (fun i =>
      ((listed.drop (i * 4)).take 4) == [0,0,0,1])
    if hasOne then .ok (c, [])
    else
      .ok ({c with closedAt := some now, errorCode := some Error.unsupported.code},
        [Action.closed Error.unsupported.code])
  | .retry =>
    let retryBytes := bytes.extract pos bytes.size
    match Crypto.Quic.retryCheck c.firstDcid.toArray retryBytes with
    | .ok _ =>
      let armed ← armClientInitial {c with dcid := (bytes.extract packet.scid.offset (packet.scid.offset + packet.scid.length)).toList, retryToken := (bytes.extract packet.token.offset (packet.token.offset + packet.token.length)).toList}
      -- resend the ClientHello under the new keys and the Retry token
      let out := outOf armed .initial
      let resent ← out.append armed.tls.chBytes c.limits.cryptoBufferBytes
      .ok (setOutOf armed .initial resent, [])
    | .error _ => .ok (c, []) -- integrity failure drops the packet
  | .unsupported => .ok (c, [])
  | _ =>
    match kindLevel packet.kind with
    | .error _ => .ok (c, [])
    | .ok level =>
      let prearmed ←
        match level with
        | .initial =>
          if c.role == .server && (spaceOf c .initial).peerKey.isNone then
            let keyDcid := (bytes.extract packet.dcid.offset (packet.dcid.offset + packet.dcid.length)).toList
            let clientCid := (bytes.extract packet.scid.offset (packet.scid.offset + packet.scid.length)).toList
            match armServerInitial c keyDcid with
            | .ok armed =>
              .ok {armed with dcid := clientCid, tls := {armed.tls with originalDcid := keyDcid}}
            | .error e2 => throw (Error.coded (32002 + e2.code))
          else .ok c
        | _ => .ok c
      let keyedConn ←
        match level, prearmed.role with
        | .initial, Role.client =>
          let serverCid := (bytes.extract packet.scid.offset (packet.scid.offset + packet.scid.length)).toList
          .ok {prearmed with tls := {prearmed.tls with linkScid := serverCid}}
        | _, _ => .ok prearmed

      let space := spaceOf keyedConn level
      match kindLevel packet.kind with
      | .error _ => pure () -- version negotiation / retry: no protected payload
      | .ok _ => if space.peerKey.isNone then throw (.coded 41001)
      let decrypted ← decryptPacket keyedConn space level packet bytes pos
      match decrypted with
      | none => .ok (c, []) -- unauthenticated bytes are dropped, never fatal
      | some (d, openable) =>
        let keyed := if openable != space then setSpacing keyedConn level openable else keyedConn
          let dup := (spaceOf keyed level).seen.contains d.number
          if dup then
            .ok (keyed, []) -- duplicate applies no semantics
          else
            let validated := if keyed.role == .client && level != .initial then
              {keyed with peerValidated := true} else keyed
            let (withFrames, frameActions) ← processFrames validated level d.payload now
            -- ACK-only and PADDING-only bytes are not ack-eliciting (RFC 9002 6.2);
            -- receiving them must not arm an acknowledgment in reply.
            let spaced := recordPn (spaceOf keyed level) d.number keyed.limits.trackedPacketNumbers
            let effective := {spaced with ackPending := ackEliciting d.payload}
            let recorded := setSpaceOf withFrames level effective
            let (advanced, tlsActions) ← advance recorded
            .ok (advanced, frameActions ++ tlsActions)

/-- Process a coalesced datagram. -/
def onDatagram (c : Conn) (bytes : List UInt8) (now : Nat) :
    Except Error (Conn × List Action) := do
  if c.closedAt.isSome then return (c, [])
  if bytes.length > maxDatagram then return (c, [])
  let mut state := setClock c now
  if state.role == .server && !state.peerValidated then
    state := {state with unvalidatedRx := state.unvalidatedRx + bytes.length}
  let shortLength := state.scid.length
  match (Except.mapError (fun e => Error.coded (41100 + e.code))
    (Spec.Quic.Wire.parsePackets bytes.toArray shortLength c.limits.maxRxBatch)) with
  | .error e2 => throw e2
  | .ok packets =>
    let mut actions : List Action := []
    for pair in packets do
      let (pos, packet) := pair
      let (next, batch) ← onPacket state packet bytes.toArray pos now
      state := next
      actions := actions ++ batch
      if state.closedAt.isSome then break
    let (final, more) ← advance state
    return (final, actions ++ more)

/-- Loss timing: RFC 9002 initial RTT with doubling backoff, bounded at 2^10
per connection. This profile samples no RTT; the recovery leaves refine the
full timing math (see Tests/Recovery). -/
def ptoInterval (c : Conn) : Nat :=
  (353000000 : Nat) * 2^(min c.lossCount 10)

/-- PTO probe: repacketize the crypto ranges and stream payloads of the oldest
unacked record per level with fresh packet numbers, coalesced into datagrams.
Crypto bytes come from the sent log; stream payloads re-reserve from the
immutable send state. Raw ciphertext is never reused. -/
def stepPto (c : Conn) : Except Error (Conn × List Action) := do
  if c.closedAt.isSome then return (c, [])
  let mut state := c
  let mut wire : List UInt8 := []
  let mut due := false
  for level in levelOrder do
    let space := spaceOf state level
    match space.unacked with
    | oldest :: _ =>
      unless state.now < oldest.sentAt + ptoInterval state do
        due := true
        let log := logOf state level
        let mut body : List UInt8 := []
        for (start, len) in oldest.crypto do
          match cryptoFrame start (log.drop start |>.take len) with
          | .ok f => body := body ++ f
          | .error _ => pure ()
        let mut reserved : List (StreamEntry × Spec.Stream.Range) := []
        for (id, start, len, fin) in oldest.streams do
          match state.streams.find? (fun e => e.id == id) with
          | some entry =>
            if entry.send.pending.isNone then
              match Spec.Stream.Send.reserve entry.send
                  {start := start, length := len, fin := fin} with
              | .ok (send', _) =>
                let bytes := (entry.send.data.drop (start - entry.send.base)).take len
                body := body ++ (← streamFrame id start fin bytes)
                let committed := {entry with send := send'}
                reserved := (committed, {start := start, length := len, fin := fin}) :: reserved
                state := {state with streams := state.streams.map (fun e =>
                  if e.id == id then committed else e)}
              | .error _ => pure ()
          | none => pure ()
        if body.isEmpty then
          -- only acks pending? send a plain ack-eliciting probe
          body := pingFrame
        let draft : Draft := Draft.mk level body 0 0 oldest.crypto (oldest.streams.map (fun (i, s, l, f) => (i, s, l, f))) false 0
        if wire.length + 40 + draft.plain.length ≤ maxDatagram then
          let bundle : DraftBundle := {level := level, draft := draft, reserved := reserved}
          let (committed, bytes) ← protectBundle state bundle
          wire := if wire.isEmpty then bytes else wire ++ bytes
          state := {committed with lossCount := state.lossCount + 1, lossAt := committed.now + ptoInterval committed}
        else
          state := releaseReservations state reserved
    | [] => pure ()
  if !due || wire.isEmpty then return (state, [])
  return (state, [Action.sendDatagram wire])

/-- The number of bytes before which this connection may not send to an
unvalidated peer. -/
def amplificationBudget (c : Conn) : Nat :=
  if c.role == .server && !c.peerValidated then
    let cap := 3 * c.unvalidatedRx
    cap - (min cap c.unvalidatedTx)
  else maxDatagram

/-- The listener's bootstrap step: request entropy for random, certificate
seed and X25519 secret. The runtime calls this once per admitted connection. -/
def listenerStart (c : Conn) : Except Error (Conn × List Action) := do
  if c.role != .server then throw .state
  if c.closedAt.isSome || c.entropyOutstanding then throw .busy
  let freshConn : Conn := {
    c with
    entropyOutstanding := true
    entropyRequestId := c.entropyRequestId + 1
    handshakeDeadline := c.now + c.limits.handshakeTimeoutNs
    idleDeadline := c.now + c.limits.idleTimeoutNs
  }
  return (freshConn, [Action.entropyRequest freshConn.entropyRequestId
    entropyRequestLength])

/-- Provision both roles with their 96 entropy bytes: 32 random for the
handshake, 32 per-connection certificate seed, 32 X25519 secret. Returns the
issued certificate for the TLS state. -/
def provision (c : Conn) (bytes : List UInt8) :
    Except Error (Tls × Identity.Certificate.Issued) := do
  unless bytes.length == entropyRequestLength do throw .limit
  let issued ←
    match Identity.Certificate.issue c.hostKind c.hostSecret
        (bytes.drop 32 |>.take 32)
        (c.utcNs / 1000000000 - 3600) (c.utcNs / 1000000000 + 604800) with
    | .ok i => .ok i
    | .error _ => .error .entropy
  let tls : Tls := {
    issued := some issued,
    random := bytes.take 32,
    ephSecret := bytes.drop 64,
    utcNs := c.utcNs,
    hostSecret := c.hostSecret
  }
  return (tls, issued)

/-- One step of the event loop. Exactly one event is processed; the returned
action list stays within `Limits.maxActions`. -/
def step (c : Conn) (event : Event) : Except Error (Conn × List Action) := do
  match event with
  | Event.clock wallNs =>
    return ({c with utcNs := wallNs}, [])
  | Event.dial peerId =>
    if c.role != .client then throw .state
    if c.closedAt.isSome then throw .closed
    if c.entropyOutstanding || c.entropyRequestId > 0 then throw .busy
    let freshConn : Conn := {
      c with
      expectedPeer := peerId,
      tls := {c.tls with expectedPeer := peerId, utcNs := c.utcNs},
      entropyOutstanding := true,
      entropyRequestId := c.entropyRequestId + 1,
      handshakeDeadline := c.now + c.limits.handshakeTimeoutNs,
      idleDeadline := c.now + c.limits.idleTimeoutNs
    }
    return (freshConn, [Action.entropyRequest freshConn.entropyRequestId
      entropyRequestLength])
  | Event.entropyReady requestId ok bytes =>
    if requestId != c.entropyRequestId || !c.entropyOutstanding then throw .stale
    match ok, bytes.length == entropyRequestLength with
    | false, _ =>
      return ({c with closedAt := some c.now, errorCode := some Error.entropy.code},
        [Action.closed Error.entropy.code])
    | true, false =>
      return ({c with closedAt := some c.now, errorCode := some Error.entropy.code},
        [Action.closed Error.entropy.code])
    | true, true =>
      let (tls, _) ← provision c bytes
      let tlsClient : Tls := {tls with localScid := deriveCid bytes 3, originalDcid := if c.role == .client then deriveCid bytes 1 else [], expectedPeer := c.expectedPeer}
      match c.role with
      | .client =>
        let armed ← armClientInitial {c with tls := tlsClient, dcid := deriveCid bytes 1, firstDcid := deriveCid bytes 1}
        let (started, flights) ← clientStart armed.tls armed.limits
        let mut state := {armed with tls := started, entropyOutstanding := false, scid := deriveCid bytes 3}
        for f in flights do
          let out := outOf state f.level
          let appended ← out.append f.bytes state.limits.cryptoBufferBytes
          state := setOutOf state f.level appended
        let (sent, actions) ← emitRound state
        return (sent, List.reverse actions)
      | .server =>
        -- The server arms Initial keys only upon the first ClientHello's
        -- destination CID; nothing to arm from empty credentials here.
        let serverTls : Tls := {tlsClient with localScid := deriveCid bytes 4}
        let state := {c with tls := serverTls, entropyOutstanding := false, scid := deriveCid bytes 4}
        return (state, [])
  | Event.receiveDatagram now bytes =>
    let handled ←
      match onDatagram c bytes now with
      | .ok v => .ok v
      | .error e2 => .error e2
    let (state, actions) := handled
    let refreshed := {state with idleDeadline := now + c.limits.idleTimeoutNs}
    if refreshed.closedAt.isSome then
      return (refreshed, List.reverse actions)
    let emitted ←
      match emitRound refreshed with
      | .ok v => .ok v
      | .error e => .error (.coded (45001 : Nat))
    let (emitted, more) := emitted
    if more.isEmpty then
      return (refreshed, List.reverse actions)
    else
      return (emitted, List.reverse (actions ++ more))
  | Event.sendResult token outcome =>
    let pending := c.pendingSends.filter (fun p => p.1 != token)
    if pending.length == c.pendingSends.length && outcome != 0 then
      throw .stale
    if outcome == 0 then
      return ({c with pendingSends := pending}, [])
    else
      let attempts := c.sendAttempts + 1
      if attempts > c.limits.maxSendAttempts then
        return ({c with closedAt := some c.now, errorCode := some Error.limit.code},
          [Action.closed Error.limit.code])
      else
        let resent := c.pendingSends.filter (fun p => p.1 == token)
        let fresh := resent.map (fun p => (c.sendToken + 1, p.2))
        let actions := fresh.map (fun p => Action.sendDatagram p.2)
        return ({
          c with
          pendingSends := pending ++ fresh,
          sendToken := c.sendToken + fresh.length,
          sendAttempts := attempts
        }, List.reverse actions)
  | Event.timerExpired id now =>
    if c.closedAt.isSome then return (c, [])
    if id == timerIdle then
      if c.now >= c.idleDeadline then
        return ({c with closedAt := some c.now, errorCode := some Error.timeout.code},
          [Action.closed Error.timeout.code])
      else
        return (c, [])
    else if id == timerHandshake then
      if c.tls.phase == Phase.done || c.tls.phase == Phase.waitClient then
        return (c, [])
      else if c.now >= c.handshakeDeadline then
        return ({c with closedAt := some c.now, errorCode := some Error.timeout.code},
          [Action.closed Error.timeout.code])
      else
        return (c, [])
    else if id == timerLoss then
      let (state, actions) ← stepPto c
      return (state, List.reverse actions)
    else
      throw .stale
  | Event.ping bytes =>
    if c.closedAt.isSome then throw .closed
    unless bytes.length == 32 do throw .malformed
    let matchEntry := c.streams.find? (fun e => e.id == 0)
    match matchEntry with
    | none => throw .state
    | some e =>
      let selected := match e.multistream with
        | some m => m.phase == Spec.Multistream.Phase.selected
        | none => false
      unless selected && c.confirmed do throw .state
      if e.ping.isSome then throw .busy
      let staged : Spec.Ping.State := {
        outbound := true
        phase := 0
        deadline := c.now + c.limits.pingTimeoutNs
        entropyToken := 0
        authenticated := c.authenticated
        handshakeConfirmed := c.confirmed
      }
      let began ←
        match Spec.Ping.begin staged bytes 0 c.now with
        | .ok state2 => .ok state2
        | .error _ => .error .timeout
      let send ←
        match e.send.append bytes true with
        | .ok s => .ok s
        | .error _ => .error .limit
      let updated : StreamEntry := {e with ping := some began, send := send}
      let state := {c with streams := c.streams.map (fun x =>
        if x.id == 0 then updated else x)}
      let (sent, actions) ← emitRound state
      return (sent, List.reverse actions)
  | Event.close =>
    if c.closedAt.isSome then return (c, [])
    let level := if (spaceOf c .application).key.isNone then .initial else .application
    let space := spaceOf c level
    if space.key.isNone then
      return ({c with closedAt := some c.now, errorCode := none},
        [Action.closed 0])
    else
      let frame ← closeFrame 0 []
      let draft : Draft := Draft.mk level frame 0 0 [] [] false 0
      let (state, bytes) ← protectBundle c {level := level, draft := draft, reserved := []}
      let overBudget := state.role == .server && !state.peerValidated &&
        state.unvalidatedTx + bytes.length > 3 * state.unvalidatedRx
      if overBudget then
        return ({c with closedAt := some c.now, errorCode := none},
          [Action.closed 0])
      else
        return ({state with closedAt := some state.now, errorCode := none},
          [Action.sendDatagram bytes, Action.closed 0])

end Libp2pAsm.Spec.Connection
