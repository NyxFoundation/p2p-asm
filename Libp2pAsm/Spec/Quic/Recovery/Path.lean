import Libp2pAsm.Spec.Quic.Recovery.Ack

namespace Libp2pAsm.Spec.Quic.Recovery

def receiveBytes (s : State) (now path bytes : Nat) : Transition := do
  ready s now
  let p ← getPath s path
  let received ← checked (p.received+bytes)
  return ({s with now, paths := s.paths.set! path {p with received}}, {})

/-- Caller supplies cryptographically secure entropy. No randomness is generated
here. A live token cannot be overwritten, and response must match this path. -/
def challenge (s : State) (now path token expiry : Nat) : Transition := do
  ready s now
  let p ← getPath s path
  unless now < expiry && expiry < wordLimit && token < wordLimit do throw .malformed
  unless !p.challengeLive || p.challengeExpiry ≤ now do throw .blocked
  return ({s with now, paths := s.paths.set! path {p with challenge := token, challengeExpiry := expiry, challengeLive := true}}, {})

def response (s : State) (now path generation token : Nat) : Transition := do
  ready s now
  let p ← getPath s path
  unless p.generation == generation && p.challengeLive && p.challenge == token do throw .stale
  unless now < p.challengeExpiry do throw .expired
  return ({s with now, paths := s.paths.set! path {p with validated := true, challengeLive := false}}, {})

/-- For transport address validation (e.g. authenticated token/Handshake proof),
not TLS identity authentication. No authentication state exists in recovery. -/
def validatePath (s : State) (now path generation : Nat) : Transition := do
  ready s now
  let p ← getPath s path
  unless p.generation == generation do throw .stale
  return ({s with now, paths := s.paths.set! path {p with validated := true}}, {})

def newPath (s : State) (now index generation : Nat) : Transition := do
  ready s now
  let some p := s.paths[index]? | throw .malformed
  unless !p.used do throw .state
  unless 0 < generation && generation < wordLimit do throw .exhausted
  return ({s with now, paths := s.paths.set! index (pathInitial generation s.config.datagram now)}, {})

def activatePath (s : State) (now index generation : Nat) : Transition := do
  ready s now
  let p ← getPath s index
  unless p.generation == generation do throw .stale
  unless p.validated do throw .state
  return ({s with now, activePath := index, ptoCount := 0}, {})

def handshake (s : State) (now : Nat) (complete confirmed peerValidated : Bool) : Transition := do
  ready s now
  unless (!s.complete || complete) && (!s.confirmed || confirmed) &&
    (!confirmed || complete) && (!s.peerValidated || peerValidated) do throw .malformed
  return ({s with now, complete, confirmed, peerValidated}, {})

/-- Explicit bounded persistent-congestion certificate validation. The caller
selects two lost eliciting records, then EVERY record is examined; no caller
assertion of congestion is trusted. This is a pure predicate, not a runtime oracle. -/
def persistent (s : State) (a b : Nat) : Bool := Id.run do
  let some first := s.packets[a]? | return false
  let some last := s.packets[b]? | return false
  let p := s.paths[first.path]!
  if !(first.status == 5 && last.status == 5 && first.eliciting && last.eliciting &&
    first.path == last.path && p.samples > 0 && p.firstSample < first.sentAt &&
    first.sentAt < last.sentAt && persistentDuration s p < last.sentAt-first.sentAt) then return false
  return s.packets.all fun packet =>
    !(packet.evidence && packet.path == first.path && first.sentAt ≤ packet.sentAt &&
      packet.sentAt ≤ last.sentAt) || packet.status == 5

def collapse (s : State) (now a b : Nat) : Transition := do
  ready s now
  unless persistent s a b do throw .state
  let packet := s.packets[b]!
  let p := s.paths[packet.path]!
  unless p.persistentApplied < packet.sentAt do throw .stale
  return ({s with now, paths := s.paths.set! packet.path {p with cwnd := 2*p.mtu, minimum := p.latest, recovering := false, persistentApplied := packet.sentAt}}, {})

def installKeys (s : State) (now space : Nat) : Transition := do
  ready s now
  let some sp := s.spaces[space]? | throw .malformed
  unless !sp.discarded do throw .state
  let keys := if s.keys / 2^space % 2 == 1 then s.keys else s.keys+2^space
  return ({s with now, keys}, {})

end Libp2pAsm.Spec.Quic.Recovery
