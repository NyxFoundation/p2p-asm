import Libp2pAsm.Spec.Quic.Recovery.Send

namespace Libp2pAsm.Spec.Quic.Recovery

/-- Delay is microseconds on the wire, nanoseconds here. Ignore delay entirely
before confirmation and outside Application; this is permitted by RFC9002 §5.3. -/
def ackDelay (c : Config) (confirmed : Bool) (space raw : Nat) : Nat :=
  if confirmed && space == 2 then min c.maxAckDelayNs (raw*2^c.exponent*1000) else 0

def updateRtt (p : Path) (now sent delay : Nat) : Except Error Path := do
  unless sent ≤ now do throw .malformed
  let latest := now-sent
  if p.samples == 0 then
    return {p with latest, minimum := latest, smoothed := latest, variance := latest/2, samples := 1, firstSample := now}
  let samples ← checked (p.samples+1)
  let minimum := min p.minimum latest
  let adjusted := if minimum+delay ≤ latest then latest-delay else latest
  let difference := max p.smoothed adjusted - min p.smoothed adjusted
  return {p with latest, minimum, samples, variance := (3*p.variance+difference)/4, smoothed := (7*p.smoothed+adjusted)/8}

def lossDelay (p : Path) : Nat := max granularity ((9*max p.latest p.smoothed + 7)/8)
def ptoDuration (s : State) (p : Path) (space : Nat) : Nat :=
  (p.smoothed + max (4*p.variance) granularity +
    if space == 2 && s.confirmed then s.config.maxAckDelayNs else 0)*2^s.ptoCount

def persistentDuration (s : State) (p : Path) : Nat :=
  3*(p.smoothed + max (4*p.variance) granularity + s.config.maxAckDelayNs)

def onAck (p : Path) (packet : Packet) : Except Error Path := do
  if !packet.inFlight || packet.status != 3 then return p
  let flight := p.flight-packet.bytes
  if (p.recovering && packet.sentAt ≤ p.recoveryStart) || packet.limited then
    return {p with flight}
  let increment := if p.cwnd < p.ssthresh then packet.bytes else p.mtu*packet.bytes/p.cwnd
  let cwnd ← checked (p.cwnd+increment)
  return {p with flight, cwnd}

def onLoss (p : Path) (packet : Packet) (now : Nat) : Path :=
  if !packet.inFlight then p else
  let p := {p with flight := p.flight-packet.bytes}
  if p.recovering && packet.sentAt ≤ p.recoveryStart then p else
  let cwnd := max (2*p.mtu) (p.cwnd/2)
  {p with cwnd, ssthresh := cwnd, recovering := true, recoveryStart := now}

/-- Earliest nonzero loss deadline wins, then PTO. No application PTO before
confirmation. A server unable to reserve even one MTU suppresses PTO. -/
def timer (s : State) (now : Nat) : Except Error Action := do
  ready s now
  let mut loss := 0
  let mut which := 0
  for i in [:3] do
    let sp := s.spaces[i]!
    if !sp.discarded && sp.lossTime != 0 && (loss == 0 || sp.lossTime < loss) then
      loss := sp.lossTime
      which := i
  if loss != 0 then return {kind := 11, index := which, time := loss, token := 1}
  let path ← getPath s s.activePath
  let mut deadline := 0
  let mut owner := s.activePath
  for i in [:3] do
    let sp := s.spaces[i]!
    if !sp.discarded && s.keys / 2^i % 2 == 1 && sp.outstanding > 0 && (i != 2 || s.confirmed) then
      let mut candidate := s.activePath
      for packet in s.packets do
        if packet.evidence && packet.eliciting && packet.space == i && packet.sentAt == sp.lastEliciting then
          candidate := packet.path
      let sendingPath := s.paths[candidate]!
      if amplificationAllows s.server sendingPath 1200 then
        let t ← checked (sp.lastEliciting + ptoDuration s sendingPath i)
        if deadline == 0 || t < deadline then deadline := t; which := i; owner := candidate
  if deadline == 0 && !s.server && !s.peerValidated then
    which := if s.spaces[1]!.discarded || s.keys / 2 % 2 == 0 then 0 else 1
    if s.spaces[which]!.discarded || s.keys / 2^which % 2 == 0 then return {}
    deadline ← checked (path.ptoAnchor + ptoDuration s path which)
  return if deadline == 0 then {} else {kind := 11, index := which, time := deadline, token := 2, frames := owner}

def firePto (s : State) (now deadline space : Nat) : Transition := do
  let t ← timer s s.now
  unless t.kind == 11 && t.token == 2 && t.time == deadline && t.index == space do throw .stale
  unless deadline ≤ now && s.now ≤ now do throw .malformed
  unless s.ptoCount < 63 do throw .exhausted
  let path ← getPath s t.frames
  unless path.probeCredits == 0 do throw .blocked
  let _ ← checked (ptoDuration {s with ptoCount := s.ptoCount+1} path space)
  return ({s with now, ptoCount := s.ptoCount+1, paths := s.paths.set! t.frames {path with probeCredits := 2, probeSpace := space+1, ptoAnchor := now}},
    {kind := 12, index := space, token := 2, time := now, frames := t.frames})

end Libp2pAsm.Spec.Quic.Recovery
