import Libp2pAsm.Spec.Quic.Recovery.Types

namespace Libp2pAsm.Spec.Quic.Recovery

structure Send where
  space : Nat
  path : Nat
  bytes : Nat
  inFlight : Bool
  eliciting : Bool
  frames : Nat
  frameGeneration : Nat
  buffer : Nat
  bufferGeneration : Nat
  probe : Bool := false
  limited : Bool := false
  deriving Repr, BEq, Inhabited

def amplificationAllows (server : Bool) (p : Path) (bytes : Nat) : Bool :=
  !server || p.validated || p.transmitted+p.reserved+bytes ≤ 3*p.received

def reserve (s : State) (now : Nat) (e : Send) : Transition := do
  ready s now
  let space ← getSpace s e.space
  let path ← getPath s e.path
  unless space.pendingPlus == 0 do throw .blocked
  unless 0 < e.bytes && e.bytes ≤ path.mtu && (!e.eliciting || e.inFlight) do throw .malformed
  unless space.next < pnLimit && s.nextAttempt < wordLimit-1 do throw .exhausted
  unless s.packets.size < s.config.history do throw .capacity
  unless s.pending < s.config.pending && s.live < s.config.live do throw .blocked
  unless amplificationAllows s.server path e.bytes do throw .blocked
  unless !e.inFlight || e.probe || path.flight+path.reservedFlight+e.bytes ≤ path.cwnd do
    throw .blocked
  unless !e.probe || (e.eliciting && 0 < path.probeCredits && path.probeSpace == e.space+1) do throw .malformed
  unless !e.inFlight || e.probe || path.paceAt ≤ now do throw .blocked
  let deadline ← checked (now+s.config.waitNs)
  let reserved ← checked (path.reserved+e.bytes)
  let reservedFlight ← checked (path.reservedFlight+if e.inFlight then e.bytes else 0)
  let p : Packet := { status := 1, space := e.space, path := e.path, pn := space.next, bytes := e.bytes, inFlight := e.inFlight, eliciting := e.eliciting, frames := e.frames, frameGeneration := e.frameGeneration, buffer := e.buffer, bufferGeneration := e.bufferGeneration, attempt := s.nextAttempt, attempts := 1, first := now, deadline, attemptAt := now, limited := e.limited, probe := e.probe }
  let path := {path with reserved, reservedFlight, probeCredits := path.probeCredits - if e.probe then 1 else 0}
  let space := {space with next := space.next+1, pendingPlus := s.packets.size+1}
  return ({s with now, nextAttempt := s.nextAttempt+1, pending := s.pending+1, live := s.live+1, spaces := s.spaces.set! e.space space, paths := s.paths.set! e.path path, packets := s.packets.push p}, packetAction 1 s.packets.size p)

def release (s : State) (i status : Nat) (p : Packet) : State :=
  let path := s.paths[p.path]!
  let space := s.spaces[p.space]!
  {s with pending := s.pending-1, live := s.live-1, paths := s.paths.set! p.path {path with reserved := path.reserved-p.bytes, reservedFlight := path.reservedFlight-(if p.inFlight then p.bytes else 0)}, spaces := s.spaces.set! p.space {space with pendingPlus := 0}, packets := s.packets.set! i {p with status}}

/-- OS completion time is distinct from event delivery time. Failed or blocked
trials must NEVER subsequently send. Unknown outcomes retain reservation. -/
def successful (s : State) (i now sentAt : Nat) (p : Packet) : Transition := do
  unless p.attemptAt ≤ sentAt && sentAt ≤ now do throw .host
  let path := s.paths[p.path]!
  let space := s.spaces[p.space]!
  unless space.sentPlus ≤ p.pn do throw .host
  let transmitted ← checked (path.transmitted+p.bytes)
  let flight ← checked (path.flight+if p.inFlight then p.bytes else 0)
  let spacing := if p.inFlight then (p.bytes*path.smoothed + path.cwnd-1)/path.cwnd else 0
  let paceAt ← checked (max now path.paceAt + spacing)
  let path := {path with transmitted, flight, paceAt, lastSend := max path.lastSend sentAt, reserved := path.reserved-p.bytes, reservedFlight := path.reservedFlight-(if p.inFlight then p.bytes else 0)}
  let space := {space with pendingPlus := 0, sentPlus := p.pn+1, lastEliciting := if p.eliciting then sentAt else space.lastEliciting, outstanding := space.outstanding + if p.eliciting then 1 else 0}
  return ({s with now, pending := s.pending-1, paths := s.paths.set! p.path path, spaces := s.spaces.set! p.space space, packets := s.packets.set! i {p with status := 3, sentAt, evidence := true}},
    packetAction 2 i p)

def result (s : State) (generation i token now outcome sentAt : Nat) : Transition := do
  ready s now
  unless generation == s.generation do throw .stale
  let some p := s.packets[i]? | throw .stale
  unless p.status == 1 && p.attempt == token do throw .stale
  unless now < p.deadline do throw .expired
  if outcome == 0 then return ← successful s i now sentAt p
  if outcome == 1 then
    return ({s with now, packets := s.packets.set! i {p with status := 2}}, packetAction 3 i p)
  unless outcome == 2 || outcome == 3 do throw .malformed
  let t := release s i 6 p
  let path := t.paths[p.path]!
  let failed := outcome == 3 || p.bytes ≤ 1200
  let path := {path with failed, mtu := if failed then path.mtu else min path.mtu (p.bytes-1)}
  return ({t with now, paths := t.paths.set! p.path path}, packetAction (if failed then 5 else 4) i p)

/-- Called only in response to host writability, never from a busy retry loop. -/
def retry (s : State) (generation i now : Nat) : Transition := do
  ready s now
  unless generation == s.generation do throw .stale
  let some p := s.packets[i]? | throw .stale
  unless p.status == 2 do throw .state
  unless now < p.deadline && p.attempts < s.config.attempts do throw .expired
  unless s.nextAttempt < wordLimit-1 do throw .exhausted
  let _ ← getPath s p.path
  let p := {p with status := 1, attempt := s.nextAttempt, attempts := p.attempts+1, attemptAt := now}
  return ({s with now, nextAttempt := s.nextAttempt+1, packets := s.packets.set! i p},
    packetAction 1 i p)

/-- Timeout is independent of writability. Unknown host ownership is quarantined:
neither the registry loan nor amplification reservation is freed on this branch. -/
def expire (s : State) (generation i now : Nat) : Transition := do
  unless s.retired == 0 do throw .retired
  unless s.now ≤ now && now < wordLimit do throw .malformed
  unless generation == s.generation do throw .stale
  let some p := s.packets[i]? | throw .stale
  unless p.status == 1 || p.status == 2 do throw .stale
  unless p.deadline ≤ now || (p.status == 2 && p.attempts ≥ s.config.attempts) do throw .blocked
  let s := if s.batch.phase == 0 then s else {s with batch := {}, retired := 8}
  if p.status == 2 then
    let t := release s i 6 p
    return ({t with now, paths := t.paths.set! p.path {t.paths[p.path]! with failed := true}}, packetAction 5 i p)
  return ({s with now, retired := 9, packets := s.packets.set! i {p with status := 7}},
    packetAction 6 i p)

end Libp2pAsm.Spec.Quic.Recovery
