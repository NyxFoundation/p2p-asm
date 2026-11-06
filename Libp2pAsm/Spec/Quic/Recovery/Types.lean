import Std

namespace Libp2pAsm.Spec.Quic.Recovery

def wordLimit : Nat := 2^64
def pnLimit : Nat := 2^62
def granularity : Nat := 1000000
def initialRtt : Nat := 333000000
def magic : Nat := 0x5245434f5631

/-- Numeric status is also the public RV64 a0 result. -/
inductive Error where
  | malformed | exhausted | memory | capacity | stale | blocked | expired
  | host | state | busy | unsentAck | retired
  deriving Repr, BEq, DecidableEq

def Error.code : Error → Nat
  | .malformed => 2 | .exhausted => 3 | .memory => 4 | .capacity => 5
  | .stale => 6 | .blocked => 7 | .expired => 8 | .host => 9
  | .state => 10 | .busy => 11 | .unsentAck => 12 | .retired => 13

/-- All quantities are natural numbers; checked conversion to LE64 is at the ABI.
No limit defaults are hidden here. Limits mapping is documented in Tests/Recovery. -/
structure Config where
  history : Nat
  paths : Nat
  ranges : Nat
  pending : Nat
  live : Nat
  attempts : Nat
  waitNs : Nat
  datagram : Nat
  quantum : Nat
  exponent : Nat
  maxAckDelayNs : Nat
  deriving Repr, BEq, Inhabited

def contextWords (c : Config) : Nat := 64 + 32*c.paths + 20*c.history + 2*c.ranges
def quantumBound (c : Config) : Nat := 200000 + 100*contextWords c + 500*c.history*c.paths

def Config.valid (c : Config) : Bool :=
  [c.history,c.paths,c.ranges,c.pending,c.live,c.attempts,c.waitNs,c.quantum].all
    (fun x => 0 < x && x < wordLimit) &&
  c.pending ≤ c.live && c.live ≤ c.history && 1200 ≤ c.datagram && c.datagram ≤ 65507 &&
  c.exponent ≤ 20 && c.maxAckDelayNs < 16384*1000000 &&
  c.history ≤ (wordLimit-1)/16000 && c.paths ≤ (wordLimit-1)/25600 &&
  c.ranges ≤ (wordLimit-1)/1600 &&
  8*contextWords c < wordLimit && quantumBound c ≤ c.quantum

structure Space where
  next : Nat := 0
  discarded : Bool := false
  ackPlus : Nat := 0
  lastEliciting : Nat := 0
  outstanding : Nat := 0
  pendingPlus : Nat := 0
  sentPlus : Nat := 0
  lossTime : Nat := 0
  deriving Repr, BEq, Inhabited

structure Path where
  used : Bool := false
  generation : Nat := 0
  validated : Bool := false
  received : Nat := 0
  transmitted : Nat := 0
  reserved : Nat := 0
  flight : Nat := 0
  reservedFlight : Nat := 0
  cwnd : Nat := 0
  ssthresh : Nat := wordLimit-1
  recoveryStart : Nat := 0
  recovering : Bool := false
  latest : Nat := 0
  minimum : Nat := 0
  smoothed : Nat := initialRtt
  variance : Nat := initialRtt/2
  samples : Nat := 0
  firstSample : Nat := 0
  paceAt : Nat := 0
  lastSend : Nat := 0
  challenge : Nat := 0
  challengeExpiry : Nat := 0
  challengeLive : Bool := false
  failed : Bool := false
  mtu : Nat := 1200
  ptoAnchor : Nat := 0
  persistentEnd : Nat := 0
  persistentCount : Nat := 0
  persistentApplied : Nat := 0
  probeCredits : Nat := 0
  probeSpace : Nat := 0
  deriving Repr, BEq, Inhabited

/-- A record is never reused within a connection generation. Status 1=pending,
2=would-block, 3=sent, 4=acked, 5=lost, 6=abandoned, 7=unknown, 8=discarded.
Frame and buffer references identify caller-owned immutable registered objects. -/
structure Packet where
  status : Nat := 0
  space : Nat := 0
  path : Nat := 0
  pn : Nat := 0
  bytes : Nat := 0
  inFlight : Bool := false
  eliciting : Bool := false
  frames : Nat := 0
  frameGeneration : Nat := 0
  buffer : Nat := 0
  bufferGeneration : Nat := 0
  attempt : Nat := 0
  attempts : Nat := 0
  first : Nat := 0
  deadline : Nat := 0
  sentAt : Nat := 0
  evidence : Bool := false
  attemptAt : Nat := 0
  limited : Bool := false
  probe : Bool := false
  deriving Repr, BEq, Inhabited

structure AckRange where
  lo : Nat
  hi : Nat
  deriving Repr, BEq, Inhabited

/-- Resumable batches freeze all other recovery mutations. Ranges are owned
copies. Phase 1 validates evidence, 2 applies ACKs, 3 detects loss, 4 discards.
Every resume consumes exactly one ledger slot or advances a finite phase. -/
structure Batch where
  phase : Nat := 0
  space : Nat := 0
  now : Nat := 0
  delay : Nat := 0
  ranges : Array AckRange := #[]
  cursor : Nat := 0
  rangeIndex : Nat := 0
  seen : Nat := 0
  largest : Nat := 0
  sampleTime : Nat := 0
  sampleNew : Bool := false
  anyEliciting : Bool := false
  anyNew : Bool := false
  deriving Repr, BEq, Inhabited

structure State where
  config : Config
  generation : Nat
  slot : Nat
  nextAttempt : Nat := 1
  pending : Nat := 0
  live : Nat := 0
  now : Nat := 0
  server : Bool := false
  complete : Bool := false
  confirmed : Bool := false
  peerValidated : Bool := false
  activePath : Nat := 0
  ptoCount : Nat := 0
  keys : Nat := 1
  retired : Nat := 0
  spaces : Array Space := Array.replicate 3 {}
  paths : Array Path
  packets : Array Packet := #[]
  batch : Batch := {}
  deriving Repr, BEq, Inhabited

/-- Eight LE64 words. Actions: 0 none, 1 send, 2 buffer-return, 3 wait-writable,
4 repacketize, 5 fail-path, 6 cancel-and-quarantine, 7 ack-frames, 8 lost-frames,
9 discard-frames, 10 continuation, 11 timer, 12 probes.
Notifications are metadata, never direct application delivery or ciphertext retry. -/
structure Action where
  kind : Nat := 0
  index : Nat := 0
  pn : Nat := 0
  token : Nat := 0
  time : Nat := 0
  frames : Nat := 0
  frameGeneration : Nat := 0
  buffer : Nat := 0
  deriving Repr, BEq, Inhabited

def packetAction (kind i : Nat) (p : Packet) : Action :=
  ⟨kind,i,p.pn,p.attempt,p.deadline,p.frames,p.frameGeneration,p.buffer⟩

abbrev Transition := Except Error (State × Action)
def checked (n : Nat) : Except Error Nat :=
  if n < wordLimit then .ok n else .error .exhausted
def initialWindow (mtu : Nat) : Nat := min (10*mtu) (max (2*mtu) 14720)
def pathInitial (generation mtu now : Nat) : Path :=
  { used := true, generation, mtu, ptoAnchor := now, cwnd := initialWindow mtu }

def init (c : Config) (generation slot now : Nat) (server : Bool) : Except Error State := do
  unless c.valid do throw .capacity
  unless 0 < generation && generation < wordLimit && slot < wordLimit && now < wordLimit do
    throw .malformed
  return { config := c, generation := generation, slot := slot, now := now, server := server, paths := (Array.replicate c.paths {}).set! 0 (pathInitial 1 c.datagram now) }

def ready (s : State) (now : Nat) : Except Error Unit := do
  unless s.retired == 0 do throw .retired
  unless s.batch.phase == 0 do throw .busy
  unless s.now ≤ now && now < wordLimit do throw .malformed

def getPath (s : State) (i : Nat) : Except Error Path := do
  let some p := s.paths[i]? | throw .malformed
  unless p.used && !p.failed do throw .state
  return p

def getSpace (s : State) (i : Nat) : Except Error Space := do
  let some p := s.spaces[i]? | throw .malformed
  unless !p.discarded && s.keys / 2^i % 2 == 1 do throw .state
  return p

end Libp2pAsm.Spec.Quic.Recovery
