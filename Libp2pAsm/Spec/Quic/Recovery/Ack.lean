import Libp2pAsm.Spec.Quic.Recovery.Timing

namespace Libp2pAsm.Spec.Quic.Recovery

def rangesValid (ranges : Array AckRange) : Bool := Id.run do
  let mut previous := pnLimit+1
  for r in ranges do
    if !(r.lo ≤ r.hi && r.hi < pnLimit && r.hi+1 < previous) then return false
    previous := r.lo
  return !ranges.isEmpty

def inRanges (ranges : Array AckRange) (pn : Nat) : Bool :=
  ranges.any (fun r => r.lo ≤ pn && pn ≤ r.hi)

def beginAck (s : State) (now space delay : Nat) (ranges : Array AckRange) : Transition := do
  ready s now
  let _ ← getSpace s space
  unless ranges.size ≤ s.config.ranges do throw .capacity
  unless delay < pnLimit && rangesValid ranges do throw .malformed
  return ({s with now, batch := { phase := 1, space, now, delay, ranges, largest := ranges[0]!.hi }}, {kind := 10})

def finishValidation (s : State) : Transition := do
  let b := s.batch
  let sp := s.spaces[b.space]!
  if !b.anyNew then return ({s with batch := {}}, {})
  let mut t := s
  if b.sampleNew && b.anyEliciting then
    let p := s.packets[b.sampleTime]!
    let path ← updateRtt s.paths[p.path]! b.now p.sentAt
      (ackDelay s.config s.confirmed b.space b.delay)
    t := {t with paths := t.paths.set! p.path path}
  return ({t with ptoCount := if b.anyNew && (s.server || s.peerValidated) then 0 else s.ptoCount, spaces := s.spaces.set! b.space {sp with ackPlus := max sp.ackPlus (b.largest+1), lossTime := 0}, batch := {b with phase := 3, cursor := 0}}, {kind := 10})

def validateOne (s : State) : Transition := do
  let b := s.batch
  if b.rangeIndex == b.ranges.size then return ← finishValidation s
  let r := b.ranges[b.rangeIndex]!
  if b.cursor == s.packets.size then
    unless b.seen == r.hi-r.lo+1 do throw .unsentAck
    return ({s with batch := {b with cursor := 0, seen := 0, rangeIndex := b.rangeIndex+1}},
      {kind := 10})
  let p := s.packets[b.cursor]!
  let matched := p.space == b.space && r.lo ≤ p.pn && p.pn ≤ r.hi
  unless !matched || (p.evidence && p.sentAt ≤ b.now) do throw .unsentAck
  let newly := matched && p.status != 4
  return ({s with batch := {b with cursor := b.cursor+1, seen := b.seen + if matched then 1 else 0, sampleNew := b.sampleNew || (newly && p.pn == b.largest), sampleTime := if matched && p.pn == b.largest then b.cursor else b.sampleTime, anyEliciting := b.anyEliciting || (newly && p.eliciting), anyNew := b.anyNew || newly}}, {kind := 10})

def acknowledgeOne (s : State) : Transition := do
  let b := s.batch
  if b.cursor == s.packets.size then
    return ({s with batch := {}}, {})
  let i := b.cursor
  let p := s.packets[i]!
  let t := {s with batch := {b with cursor := i+1}}
  if p.space != b.space || !inRanges b.ranges p.pn || p.status == 4 then return (t, {kind := 10})
  let path ← onAck s.paths[p.path]! p
  let path := {path with ptoAnchor := b.now}
  let sp := s.spaces[p.space]!
  let active := p.status == 3
  return ({t with live := t.live - if active then 1 else 0, paths := t.paths.set! p.path path, spaces := t.spaces.set! p.space {sp with outstanding := sp.outstanding - if active && p.eliciting then 1 else 0}, packets := t.packets.set! i {p with status := 4}}, packetAction 7 i p)

def lostOne (s : State) : Transition := do
  let b := s.batch
  if b.cursor == s.packets.size then
    if b.ranges.isEmpty then return ({s with batch := {}}, {})
    return ({s with batch := {b with phase := 2, cursor := 0}}, {kind := 10})
  let i := b.cursor
  let p := s.packets[i]!
  let t := {s with batch := {b with cursor := i+1}}
  let sp := s.spaces[b.space]!
  if p.space != b.space || p.status != 3 || inRanges b.ranges p.pn || sp.ackPlus == 0 || sp.ackPlus ≤ p.pn then
    return (t, {kind := 10})
  let path := s.paths[p.path]!
  let deadline ← checked (p.sentAt+lossDelay path)
  if p.pn+3 < sp.ackPlus || deadline ≤ b.now then
    return ({t with live := t.live-1, paths := t.paths.set! p.path (onLoss path p b.now), spaces := t.spaces.set! b.space {sp with outstanding := sp.outstanding - if p.eliciting then 1 else 0}, packets := t.packets.set! i {p with status := 5}}, packetAction 8 i p)
  let lossTime := if sp.lossTime == 0 then deadline else min sp.lossTime deadline
  return ({t with spaces := t.spaces.set! b.space {sp with lossTime}}, {kind := 10})

def beginLoss (s : State) (now space : Nat) : Transition := do
  ready s now
  let sp ← getSpace s space
  unless sp.lossTime != 0 && sp.lossTime ≤ now do throw .stale
  return ({s with now, spaces := s.spaces.set! space {sp with lossTime := 0}, batch := {phase := 3, now, space}}, {kind := 10})

/-- Pending outcomes must be resolved/cancelled before dropping keys. This leaf
never treats an unresolved datagram as unsent. PN allocation is never reset. -/
def beginDiscard (s : State) (now space : Nat) : Transition := do
  ready s now
  let sp ← getSpace s space
  unless space < 2 do throw .malformed
  unless sp.pendingPlus == 0 do throw .blocked
  return ({s with now, ptoCount := 0, paths := s.paths.map (fun p => if p.probeSpace == space+1 then {p with probeCredits := 0, probeSpace := 0, ptoAnchor := now} else if p.used then {p with ptoAnchor := now} else p), spaces := s.spaces.set! space {sp with discarded := true, lossTime := 0, lastEliciting := 0}, batch := {phase := 4, now, space}}, {kind := 10})

def discardOne (s : State) : Transition := do
  let b := s.batch
  if b.cursor == s.packets.size then return ({s with batch := {}}, {})
  let i := b.cursor
  let p := s.packets[i]!
  let t := {s with batch := {b with cursor := i+1}}
  if p.space != b.space || p.status != 3 then return (t, {kind := 10})
  let path := s.paths[p.path]!
  let sp := s.spaces[p.space]!
  return ({t with live := t.live-1, paths := t.paths.set! p.path {path with flight := path.flight-if p.inFlight then p.bytes else 0}, spaces := t.spaces.set! p.space {sp with outstanding := sp.outstanding-if p.eliciting then 1 else 0}, packets := t.packets.set! i {p with status := 8}}, packetAction 9 i p)

def resume (s : State) (generation : Nat) : Transition := do
  unless generation == s.generation do throw .stale
  match s.batch.phase with
  | 1 => validateOne s
  | 2 => acknowledgeOne s
  | 3 => lostOne s
  | 4 => discardOne s
  | _ => throw .state

end Libp2pAsm.Spec.Quic.Recovery
