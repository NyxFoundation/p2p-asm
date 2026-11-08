import Libp2pAsm.Spec.Tls.Schedule
import Libp2pAsm.Spec.Tls.Encode
import Libp2pAsm.Spec.Quic.Wire.Transport
import Libp2pAsm.Spec.Crypto.Curve25519.X25519
import Libp2pAsm.Spec.Crypto.Curve25519.Ed25519
import Libp2pAsm.Spec.Identity.Certificate.Issue
import Libp2pAsm.Spec.Identity.Certificate.Verify
import Libp2pAsm.Spec.Connection.Basic

/-! TLS 1.3 state machine for the libp2p-over-QUIC profile, spec layer.

One side owns message ordering, level assignment, transcript management and the
authentication gates the codec only *reports* (View obligations). There is no
record layer, no 0-RTT, no resumption, no ticket acceptance. The server does
not offer HelloRetryRequest (an X25519 share is always selected from CH1); the
client implements HRR by rewriting the transcript per RFC 8446 §4.4.1 and
resending the same ClientHello, which §4.1.2 permits because the selected group
was already offered with a share present. -/

namespace Libp2pAsm.Spec.Connection

/-- Certificate policy derived from the single `Limits` source. RSA byte
bounds cover the peer keys this profile accepts. -/
def certPolicy (l : Limits) : Identity.Certificate.Policy where
  certificateBytes := l.maxCertificateBytes
  hostPublicKeyBytes := l.maxHostPublicKeyBytes
  modulusBytes := 512
  exponentBytes := 8
  minimumRsaBits := 2048

def alpn : List UInt8 := "libp2p".toUTF8.data.toList

/-- One emitted flight: level plus raw handshake-message bytes to append to
that level's crypto send stream. -/
structure Flight where
  level : Level
  bytes : List UInt8 := []
  deriving Repr, BEq

private def be16 (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]

private def sha256 (bytes : List UInt8) : Except Error (List UInt8) :=
  match Crypto.SHA256.hash bytes with
  | .ok digest => .ok digest
  | .error _ => .error .keys

/-- Transport-parameter profile from the connection limits plus the CID
linkage. No preferred address, migration disabled. -/
def tpParameters (l : Limits) (initialScid : List UInt8)
    (originalDcid retryScid : List UInt8) : Except Error (List UInt8) := do
  match Spec.Quic.Wire.encodeProfile
    {idleTimeout := l.idleTimeoutNs / 1000000, maxUdpPayload := maxDatagram,
      maxData := l.streamReceiveBytes, bidiLocal := l.maxStreamsPerConnection,
      bidiRemote := l.maxStreamsPerConnection,
      bidiStreams := l.maxStreamsPerConnection, ackDelayExponent := 3,
      maxAckDelay := 25, activeCidLimit := max 2 l.maxActiveConnectionIds,
      initialScid := initialScid,
      originalDcid := (if originalDcid.isEmpty then none else some originalDcid),
      retryScid := (if retryScid.isEmpty then none else some retryScid),
      resetToken := none}
    (originalDcid.isEmpty == false) 4096 with
  | .ok bytes => .ok bytes
  | .error _ => .error .keys

/-- TLS handshake state; both roles use this shape, `phase` differentiates. -/
inductive Phase where
  | fresh | waitSH | waitFlight | waitClient | waitDone | done
  deriving Repr, BEq, DecidableEq

structure Tls where
  phase : Phase := .fresh
  transcript : List UInt8 := []
  utcNs : Int := 0
  hostSecret : List UInt8 := []
  issued : Option Identity.Certificate.Issued := none
  random : List UInt8 := []
  ephSecret : List UInt8 := []
  shared : List UInt8 := []
  helloDigest : List UInt8 := []
  handshake : Option Tls.Schedule.Handshake := none
  clientApp : Option (List UInt8) := none
  serverApp : Option (List UInt8) := none
  serverFinishedDigest : Option (List UInt8) := none
  finishedSent : Bool := false
  finishedSeen : Bool := false
  peerCertificate : Option (List UInt8) := none
  peerId : Option (List UInt8) := none
  chBytes : List UInt8 := []
  hrrRewritten : Bool := false
  peerSession : List UInt8 := []
  originalDcid : List UInt8 := []
  localScid : List UInt8 := []
  seenDigest : List UInt8 := []
  expectedPeer : List UInt8 := []
  linkScid : List UInt8 := []
  crSeen : Bool := false
  deriving Repr

def Tls.trafficSecret (t : Tls) (role : Role) : Option (List UInt8) :=
  match t.handshake with
  | none => none
  | some h => some ((if role == .client then h.client.toList else h.server.toList))

/-- Derive application traffic secrets after both Finished values are known.
`digest` must be Hash(ClientHello .. server Finished). -/
def Tls.deriveApplication (t : Tls) (digest : List UInt8) :
    Except Error Tls := do
  let some h := t.handshake | throw .keys
  let secrets ← Tls.Schedule.application h.master digest.toArray
    |>.mapError (fun _ => .keys)
  unless secrets.size == 64 do throw .keys
  return {
    t with
    clientApp := some (secrets.toList.take 32),
    serverApp := some (secrets.toList.drop 32),
    serverFinishedDigest := some digest
  }

private def extBytes (kind : Nat) (data : List UInt8) : Tls.Encode.Ext :=
  ⟨kind, data.toArray⟩

/-- ClientHello extension set for this profile. The client always offers
X25519 with a 32-byte share, ALPN `libp2p`, and its transport parameters. -/
def clientHelloExtensions (t : Tls) (pub : List UInt8) (l : Limits) :
    Except Error (Array Tls.Encode.Ext) := do
  let tp ← tpParameters l t.localScid [] []
  let shares := be16 (2+2+pub.length) ++ be16 29 ++ be16 pub.length ++ pub
  return #[
    extBytes 43 [0x02,0x03,0x04],
    extBytes 51 shares,
    extBytes 13 (be16 6 ++ be16 0x0403 ++ be16 0x0804 ++ be16 0x0807),
    extBytes 10 (be16 2 ++ be16 29),
    extBytes 16 (be16 (1+alpn.length) ++ [UInt8.ofNat alpn.length] ++ alpn),
    extBytes 57 tp]

private def liftTls {α : Type} (r : Except Tls.Error α) : Except Error α :=
  r.mapError (fun e => match e with
    | .needMore => .state | .malformed => .malformed
    | .unsupported => .unsupported | .address => .malformed
    | .capacity => .limit | .duplicate => .malformed
    | .profile => .unsupported | .crypto => .keys | .limit => .limit)

/-- Build and send the ClientHello. Requires the issued certificate, 32 random
bytes and 32 X25519 secret bytes to be provisioned by earlier events. -/
def clientStart (t : Tls) (l : Limits) : Except Error (Tls × List Flight) := do
  let some issued := t.issued | throw .keys
  unless t.random.length == 32 && t.ephSecret.length == 32 do throw .keys
  let pub ←
    match Crypto.Curve25519.X25519.publicKey t.ephSecret with
    | .ok v2 => .ok v2
    | .error _ => throw .keys
  let es ← clientHelloExtensions t pub l
  let raw ← liftTls (Tls.Encode.clientHello ⟨t.random.toArray, #[], #[0x13,0x01], es⟩
      l.cryptoBufferBytes)
  let ch := raw.toList
  return ({
    t with
    transcript := ch,
    chBytes := ch,
    phase := Phase.waitSH,
    issued := some issued
  }, [{level := Level.initial, bytes := ch}])

private def decodeOne (ready : Array UInt8) (limit : Nat) :
    Except Error (Option Tls.View) :=
  match Tls.decode ready limit true with
  | .ok v => .ok (some v)
  | .error .needMore => .ok none
  | .error e =>
    .error (match e with
      | .malformed => Error.malformed | .unsupported => Error.unsupported
      | .address => Error.malformed | .capacity => Error.limit
      | .duplicate => Error.malformed | .profile => Error.unsupported
      | .crypto => Error.keys | .limit => Error.limit
      | .needMore => Error.state)

private def extsOf (ready : Array UInt8) (v : Tls.View) (field : Tls.Field) :
    Except Error (Array Tls.Extension) := do
  let s := v.get field
  Tls.extensions (Tls.Cursor.mk ready s.offset (s.offset + s.length))
    |>.mapError (fun _ => .malformed)

/-- Raw bytes of a view-transport parameter; view parameters are exactly the
byte-valued IDs this profile uses for CID linkage. -/
private def tpViewBytes (input : Array UInt8)
    (parsed : Spec.Quic.Wire.Transport) (id : Nat) : Option (List UInt8) :=
  match parsed.known.lookup id with
  | some (.view v) =>
    some ((input.extract v.offset (v.offset + v.length)).toList)
  | some (.integer _) => none
  | _ => none

private def serverFlight (t : Tls) (l : Limits) (shRaw chRaw : List UInt8) :
    Except Error (Tls × List Flight) := do
  let some issued := t.issued | throw .keys
  unless t.random.length == 32 && t.ephSecret.length == 32 do throw .keys
  let tp ← tpParameters l t.localScid t.originalDcid []
  let alpnExt := extBytes 16 (be16 (1+alpn.length) ++ [UInt8.ofNat alpn.length] ++ alpn)
  let ee ←
    match Tls.Encode.encryptedExtensions #[alpnExt, extBytes 57 tp]
        l.cryptoBufferBytes with
    | .ok v2 => .ok v2
    | .error _ => throw .keys
  let cr ←
    match Tls.Encode.certificateRequest
        #[extBytes 13 (be16 6 ++ be16 0x0403 ++ be16 0x0804 ++ be16 0x0807)]
        l.cryptoBufferBytes with
    | .ok v2 => .ok v2
    | .error _ => throw .keys
  let cert ←
    match Tls.Encode.certificate issued.der.toArray #[]
        l.cryptoBufferBytes with
    | .ok v2 => .ok v2
    | .error _ => throw .keys
  let transcript1 := chRaw ++ shRaw ++ ee.toList ++ cr.toList ++ cert.toList
  let cvDigest ← sha256 transcript1
  let cvSig ←
    match Identity.Certificate.signCV issued.ephemeralSeed 2 cvDigest with
    | .ok v2 => .ok v2
    | .error _ => throw .keys
  let cv ←
    match Tls.Encode.certificateVerify 0x0807 cvSig.toArray
        l.cryptoBufferBytes with
    | .ok v2 => .ok v2
    | .error _ => throw .keys
  let transcript2 := transcript1 ++ cv.toList
  let beforeFin ← sha256 transcript2
  let some hs := t.handshake | throw .keys
  let kv ←
    match Tls.Schedule.finished hs.server beforeFin.toArray with
    | .ok v2 => .ok v2
    | .error _ => throw .keys
  unless kv.size == 64 do throw .keys
  let fin ←
    match Tls.Encode.finished (kv.extract 32 64) l.cryptoBufferBytes with
    | .ok v2 => .ok v2
    | .error _ => throw .keys
  let sfDigest ← sha256 (transcript2 ++ fin.toList)
  let out : Tls := {
    t with
    -- The server's OWN CV and Finished messages belong in the transcript
    -- (RFC 8446 §4.4: both sides hash every handshake message of the flight).
    transcript := transcript2 ++ fin.toList,
    finishedSent := true,
    finishedSeen := true,
    seenDigest := sfDigest,
    phase := Phase.waitClient
  }
  return (out, [{level := Level.initial, bytes := shRaw},
    {level := Level.handshake, bytes := ee.toList},
    {level := Level.handshake, bytes := cr.toList},
    {level := Level.handshake, bytes := cert.toList},
    {level := Level.handshake, bytes := cv.toList},
    {level := Level.handshake, bytes := fin.toList}])

/-- Accept a ClientHello at the initial level and produce the server flight:
ServerHello (initial) then EncryptedExtensions, CertificateRequest,
Certificate, CertificateVerify and Finished (handshake). -/
def serverAccept (t : Tls) (l : Limits) (level : Level)
    (ready : List UInt8) : Except Error (Tls × List Flight × Nat) := do
  unless t.phase == Phase.fresh do throw .state
  unless level == .initial do throw .state
  let some v ← decodeOne ready.toArray l.cryptoBufferBytes | return (t, [], 0)
  unless v.kind == 1 do throw .unsupported
  let some issued := t.issued | throw .keys
  unless t.random.length == 32 && t.ephSecret.length == 32 do throw .keys
  let shareBytes := (v.get .x25519).bytes ready.toArray |>.toList
  unless shareBytes.length == 32 do throw .malformed
  let shared ←
    match Crypto.Curve25519.X25519.sharedSecret t.ephSecret shareBytes with
    | .ok v2 => .ok v2
    | .error _ => throw (.coded 14004)
  let chRaw := ready.take v.consumed
  -- validate the client transport parameters and the CID linkage value
  let chExts ← extsOf ready.toArray v .extensions
  let tpEntry := chExts.find? (fun e => e.kind == 57)
  let some tpEntry := tpEntry | throw .authentication
  -- The client's parameter block must not carry server-only parameters.
  let parsed ←
    match Spec.Quic.Wire.parseTransport (tpEntry.data.bytes ready.toArray) false 64 with
    | .ok parsed => .ok parsed
    | .error _ => .error .authentication
  let _ ←
    match parsed.known.lookup 15 with
    | some (.view _) => .ok ()
    | _ => .error .authentication
  let serverPub ←
    match Crypto.Curve25519.X25519.publicKey t.ephSecret with
    | .ok v2 => .ok v2
    | .error _ => throw .keys
  let peerSession := (v.get .session).bytes ready.toArray |>.toList
  let sh ←
    match Tls.Encode.serverHello ⟨t.random.toArray, peerSession.toArray,
        #[extBytes 43 [0x03,0x04],
          extBytes 51 (be16 29 ++ be16 serverPub.length ++ serverPub)]⟩
        l.cryptoBufferBytes with
    | .ok v2 => .ok v2
    | .error _ => throw .keys
  let shRaw := sh.toList
  let transcript := chRaw ++ shRaw
  let digest ← sha256 transcript
  let handshake ←
    match Tls.Schedule.handshake shared.toArray digest.toArray with
    | .ok v2 => .ok v2
    | .error _ => throw .keys
  let staged : Tls := {
    t with
    transcript := chRaw,
    shared := shared,
    helloDigest := digest,
    handshake := some handshake,
    peerSession := peerSession,
    crSeen := true
  }
  let produced ← serverFlight {staged with transcript := transcript} l shRaw chRaw
  return (produced.1, produced.2, v.consumed)

/-- Client authentication flight: requires a CertificateRequest to have been
received, signs with the issued ephemeral Ed25519 key, and derives application
keys from the digest through the server Finished. -/
def clientFlight (t : Tls) (l : Limits) (consumed : Nat) :
    Except Error (Tls × List Flight × Nat) := do
  let some issued := t.issued | throw .keys
  unless t.crSeen do throw .unsupported
  let cert ←
    match Tls.Encode.certificate issued.der.toArray #[]
        l.cryptoBufferBytes with
    | .ok v2 => .ok v2
    | .error _ => throw .keys
  let transcript1 := t.transcript ++ cert.toList
  let cvDigest ← sha256 transcript1
  let cvSig ←
    match Identity.Certificate.signCV issued.ephemeralSeed 1 cvDigest with
    | .ok v2 => .ok v2
    | .error _ => throw (.coded (33000 + (cvDigest.take 2).foldl (fun a b => a + b.toNat) 0))
  let cv ←
    match Tls.Encode.certificateVerify 0x0807 cvSig.toArray
        l.cryptoBufferBytes with
    | .ok v2 => .ok v2
    | .error _ => throw .keys
  let selfCheck ←
    match Identity.Certificate.verifyCV (certPolicy l) issued.der 0x0807 1 cvDigest cvSig with
    | .ok v2 => .ok v2
    | .error e2 =>
      throw (.coded (34000 + Identity.Certificate.Error.code e2
        + ((cvDigest.take 2).foldl (fun a b => a + b.toNat) 0) * 64))
  let transcript2 := transcript1 ++ cv.toList
  let finDigest ← sha256 transcript2
  let some hs := t.handshake | throw .keys
  let kv ←
    match Tls.Schedule.finished hs.client finDigest.toArray with
    | .ok v2 => .ok v2
    | .error _ => throw .keys
  unless kv.size == 64 do throw .keys
  let fin ←
    match Tls.Encode.finished (kv.extract 32 64) l.cryptoBufferBytes with
    | .ok v2 => .ok v2
    | .error _ => throw .keys
  let final := transcript2 ++ fin.toList
  let out : Tls := {
    t with
    transcript := final,
    finishedSent := true,
    phase := Phase.waitDone
  }
  match selfCheck with
  | _ => pure ()
  return (out, [{level := Level.handshake, bytes := cert.toList},
     {level := Level.handshake, bytes := cv.toList},
     {level := Level.handshake, bytes := fin.toList}], consumed)

/-- Process one client-side handshake message at the handshake level. -/
def serverFeed (t : Tls) (l : Limits) (level : Level)
    (ready : List UInt8) : Except Error (Tls × List Flight × Nat) := do
  unless t.phase == Phase.waitClient do throw .state
  unless level == .handshake do throw .state
  let some v ← decodeOne ready.toArray l.cryptoBufferBytes | return (t, [], 0)
  if v.kind == 11 then
    let der := (v.get .certificate).bytes ready.toArray |>.toList
    let auth ←
      match Identity.Certificate.authenticate (certPolicy l) [der] 2 t.utcNs
        t.expectedPeer with
      | .ok v2 => .ok v2
      | .error e2 => .error (.coded (21800 + e2.code * 10 + t.transcript.length % 10))
    let transcript := t.transcript ++ ready.take v.consumed
    let _ := transcript
    let out : Tls := {
      t with
      transcript := transcript,
      peerCertificate := some der,
      peerId := some auth.peerId
    }
    return (out, [], v.consumed)
  if v.kind == 15 then
    match t.peerCertificate with
    | none => throw (.coded 21210)
    | some cert =>
      let digest ← sha256 t.transcript
      let sig := (v.get .signature).bytes ready.toArray |>.toList
      match Identity.Certificate.verifyCV (certPolicy l) cert
          v.signatureScheme 1 digest sig with
      | .ok _ => pure ()
      | .error e2 => throw (.coded (21220 + Identity.Certificate.Error.code e2
        + (((digest.take 2).foldl (fun a b => a + b.toNat) 0) * 64)))
      let transcript := t.transcript ++ ready.take v.consumed
      return ({t with transcript := transcript}, [], v.consumed)
  if v.kind == 20 then
    match t.peerCertificate with
    | none => throw (.coded 21211)
    | some cert =>
      unless t.finishedSent do throw (.coded 21212)
      let before ← sha256 t.transcript
      let some traffic := t.trafficSecret Role.client | throw (.coded 21213)
      let kv ←
        match Tls.Schedule.finished traffic.toArray before.toArray with
        | .ok v2 => .ok v2
        | .error _ => throw (.coded 21214)
      unless kv.size == 64 do throw (.coded 21215)
      unless kv.extract 32 64 == (v.get .verifyData).bytes ready.toArray do
        throw (.coded 21216)
      let transcript := t.transcript ++ ready.take v.consumed
      let keyed ← t.deriveApplication t.seenDigest
      let out : Tls := {
        keyed with
        transcript := transcript,
        finishedSeen := true,
        phase := Phase.done
      }
      return (out, [], v.consumed)
  throw .unsupported

def clientFeed (t : Tls) (l : Limits) (level : Level)
    (ready : List UInt8) : Except Error (Tls × List Flight × Nat) := do
  let some v ← decodeOne ready.toArray l.cryptoBufferBytes | return (t, [], 0)
  match t.phase with
  | .fresh => throw .state
  | .waitSH =>
    unless level == .initial do throw .state
    unless v.kind == 2 do throw .unsupported
    unless ((v.get .session).bytes ready.toArray |>.toList) == t.peerSession do
      throw .authentication
    let raw := ready.take v.consumed
    if v.hrr then
      unless !t.hrrRewritten do throw .stale
      unless v.selectedGroup == 29 do throw .unsupported
      let rewritten ←
        match Tls.Schedule.messageHash t.chBytes.toArray l.cryptoBufferBytes with
        | .ok v2 => .ok v2
        | .error _ => throw .keys
      let transcript := rewritten.toList ++ raw
      return ({t with transcript := transcript, hrrRewritten := true},
        [{level := Level.initial, bytes := t.chBytes}], v.consumed)
    unless v.selectedGroup == 29 do throw .unsupported
    let shareBytes := (v.get .x25519).bytes ready.toArray |>.toList
    unless shareBytes.length == 32 do throw .malformed
    let shared ←
      match Crypto.Curve25519.X25519.sharedSecret t.ephSecret shareBytes with
      | .ok v2 => .ok v2
      | .error _ => throw .keys
    let transcript := t.transcript ++ raw
    let digest ← sha256 transcript
    let handshake ←
      match Tls.Schedule.handshake shared.toArray digest.toArray with
      | .ok v2 => .ok v2
      | .error _ => throw .keys
    let out : Tls := {
      t with
      transcript := transcript,
      shared := shared,
      helloDigest := digest,
      handshake := some handshake,
      phase := Phase.waitFlight
    }
    return (out, [], v.consumed)
  | .waitFlight =>
    unless level == .handshake do throw .state
    if v.kind == 13 then
      -- CertificateRequest: the codec profile checked context and mask, and
      -- this FSM requires it before the client certificate flight.
      let transcript := t.transcript ++ ready.take v.consumed
      return ({t with transcript := transcript, crSeen := true}, [], v.consumed)
    if v.kind == 8 then
      for e in ← extsOf ready.toArray v .extensions do
        unless e.kind == 57 || e.kind == 16 do throw (.coded 23100)
      let tpBytes := (v.get .transportParams).bytes ready.toArray |>.toList
      unless tpBytes.length > 0 do throw (.coded 23101)
      -- The SERVER's parameter block carries the server-only CID linkage.
      let parsed ←
        match Spec.Quic.Wire.parseTransport tpBytes.toArray true 64 with
        | .ok parsed => .ok parsed
        | .error _ => .error (.coded 23102)
      match tpViewBytes tpBytes.toArray parsed 15 with
      | some scid =>
        unless scid == t.linkScid do
          throw (.coded (24000 + (scid.take 2).foldl (fun a b => a + b.toNat) 0
            + ((t.linkScid.take 2).foldl (fun a b => a + b.toNat) 0) * 300))
      | none => throw (.coded 23104)
      match tpViewBytes tpBytes.toArray parsed 0 with
      | some dcid => unless dcid == t.originalDcid do throw (.coded 23105)
      | none => throw (.coded 23106)
      let transcript := t.transcript ++ ready.take v.consumed
      return ({t with transcript := transcript}, [], v.consumed)
    if v.kind == 11 then
      let der := (v.get .certificate).bytes ready.toArray |>.toList
      let auth ←
        match Identity.Certificate.authenticate (certPolicy l) [der] 1 t.utcNs
          t.expectedPeer with
        | .ok v2 => .ok v2
        | .error _ => .error .authentication
      let transcript := t.transcript ++ ready.take v.consumed
      let out : Tls := {
        t with
        transcript := transcript,
        peerCertificate := some der,
        peerId := some auth.peerId
      }
      return (out, [], v.consumed)
    if v.kind == 15 then
      match t.peerCertificate with
      | none => throw .authentication
      | some cert =>
        let digest ← sha256 t.transcript
        let sig := (v.get .signature).bytes ready.toArray |>.toList
        match Identity.Certificate.verifyCV (certPolicy l) cert
            v.signatureScheme 2 digest sig with
        | .ok _ => pure ()
        | .error _ => throw .authentication
      let transcript := t.transcript ++ ready.take v.consumed
      return ({t with transcript := transcript}, [], v.consumed)
    if v.kind == 20 then
      let before ← sha256 t.transcript
      let some traffic := t.trafficSecret Role.server | throw .keys
      let kv ←
        match Tls.Schedule.finished traffic.toArray before.toArray with
        | .ok v2 => .ok v2
        | .error _ => throw .keys
      unless kv.size == 64 do throw .keys
      unless kv.extract 32 64 == (v.get .verifyData).bytes ready.toArray do
        throw .authentication
      let finBytes := ready.take v.consumed
      let transcript := t.transcript ++ finBytes
      -- TLS 1.3 §7.1: the application secrets hash the transcript THROUGH the
      -- peer's (server) Finished, matching the server's own sfDigest derivation.
      let digestPreFin ← sha256 transcript
      let staged ← (t.deriveApplication digestPreFin)
      let stagedTranscript : Tls := {staged with transcript := t.transcript ++ finBytes}
      let flight ← clientFlight stagedTranscript l v.consumed
      let (t2, flights, consumed) := flight
      return ({t2 with transcript := transcript}, flights, consumed)
    throw .unsupported
  | .waitDone | .waitClient | .done => throw .unsupported

end Libp2pAsm.Spec.Connection
