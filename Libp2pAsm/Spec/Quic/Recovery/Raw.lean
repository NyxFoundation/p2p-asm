import Libp2pAsm.Spec.Quic.Recovery.Path

namespace Libp2pAsm.Spec.Quic.Recovery

def bit (b : Bool) : Nat := if b then 1 else 0
def wordAt (a : Array Nat) (i : Nat) : Nat := a[i]?.getD 0

def Path.words (p : Path) : Array Nat := if !p.used then Array.replicate 32 0 else
  #[bit p.used, p.generation, bit p.validated, p.received, p.transmitted, p.reserved, p.flight, p.reservedFlight, p.cwnd, p.ssthresh, p.recoveryStart, bit p.recovering, p.latest, p.minimum, p.smoothed, p.variance, p.samples, p.firstSample, p.paceAt, p.lastSend, p.challenge, p.challengeExpiry, bit p.challengeLive, bit p.failed, p.mtu, p.ptoAnchor, p.persistentEnd, p.persistentCount, p.persistentApplied, p.probeCredits, p.probeSpace, 0]

def Path.fromWords (a : Array Nat) (offset : Nat) : Path :=
  { used := wordAt a (offset+0) != 0, generation := wordAt a (offset+1), validated := wordAt a (offset+2) != 0, received := wordAt a (offset+3), transmitted := wordAt a (offset+4), reserved := wordAt a (offset+5), flight := wordAt a (offset+6), reservedFlight := wordAt a (offset+7), cwnd := wordAt a (offset+8), ssthresh := wordAt a (offset+9), recoveryStart := wordAt a (offset+10), recovering := wordAt a (offset+11) != 0, latest := wordAt a (offset+12), minimum := wordAt a (offset+13), smoothed := wordAt a (offset+14), variance := wordAt a (offset+15), samples := wordAt a (offset+16), firstSample := wordAt a (offset+17), paceAt := wordAt a (offset+18), lastSend := wordAt a (offset+19), challenge := wordAt a (offset+20), challengeExpiry := wordAt a (offset+21), challengeLive := wordAt a (offset+22) != 0, failed := wordAt a (offset+23) != 0, mtu := wordAt a (offset+24), ptoAnchor := wordAt a (offset+25), persistentEnd := wordAt a (offset+26), persistentCount := wordAt a (offset+27), persistentApplied := wordAt a (offset+28), probeSpace := wordAt a (offset+30), probeCredits := wordAt a (offset+29) }

def Packet.words (p : Packet) : Array Nat := #[p.status, p.space, p.path, p.pn, p.bytes, bit p.inFlight, bit p.eliciting, p.frames, p.frameGeneration, p.buffer, p.bufferGeneration, p.attempt, p.attempts, p.first, p.deadline, p.sentAt, bit p.evidence, p.attemptAt, bit p.limited, bit p.probe]

def Packet.fromWords (a : Array Nat) (offset : Nat) : Packet :=
  { status := wordAt a (offset+0), space := wordAt a (offset+1), path := wordAt a (offset+2), pn := wordAt a (offset+3), bytes := wordAt a (offset+4), inFlight := wordAt a (offset+5) != 0, eliciting := wordAt a (offset+6) != 0, frames := wordAt a (offset+7), frameGeneration := wordAt a (offset+8), buffer := wordAt a (offset+9), bufferGeneration := wordAt a (offset+10), attempt := wordAt a (offset+11), attempts := wordAt a (offset+12), first := wordAt a (offset+13), deadline := wordAt a (offset+14), sentAt := wordAt a (offset+15), evidence := wordAt a (offset+16) != 0, attemptAt := wordAt a (offset+17), limited := wordAt a (offset+18) != 0, probe := wordAt a (offset+19) != 0 }

def Space.words (p : Space) : Array Nat := #[p.next, bit p.discarded, p.ackPlus, p.lastEliciting, p.outstanding, p.pendingPlus, p.sentPlus, p.lossTime]

def Space.fromWords (a : Array Nat) (offset : Nat) : Space :=
  { next := wordAt a (offset+0), discarded := wordAt a (offset+1) != 0, ackPlus := wordAt a (offset+2), lastEliciting := wordAt a (offset+3), outstanding := wordAt a (offset+4), pendingPlus := wordAt a (offset+5), sentPlus := wordAt a (offset+6), lossTime := wordAt a (offset+7) }

def State.words (s : State) : Array Nat := Id.run do
  let c := s.config
  let b := s.batch
  let mut out := #[magic,s.generation,s.slot,c.history,c.paths,c.ranges,c.pending,c.live,
    c.attempts,c.waitNs,c.datagram,c.quantum,s.packets.size,s.nextAttempt,s.pending,s.live,
    s.now,bit s.server,bit s.complete,bit s.confirmed,bit s.peerValidated,s.activePath,s.ptoCount,
    b.phase,b.space,b.now,b.delay,b.ranges.size,b.cursor,bit b.anyNew,b.largest,s.keys]
  for p in s.spaces do out := out ++ p.words
  out := out ++ #[b.sampleTime,bit b.sampleNew,bit b.anyEliciting,b.rangeIndex,b.seen,
    c.exponent,c.maxAckDelayNs,s.retired]
  for p in s.paths do out := out ++ p.words
  for i in [:c.history] do out := out ++ (s.packets[i]?.map Packet.words).getD (Array.replicate 20 0)
  for i in [:c.ranges] do
    let r := b.ranges[i]?.getD ⟨0,0⟩
    out := out ++ #[r.lo,r.hi]
  return out

def configFromWords (a : Array Nat) : Config :=
  ⟨wordAt a 3,wordAt a 4,wordAt a 5,wordAt a 6,wordAt a 7,wordAt a 8,wordAt a 9,wordAt a 10,wordAt a 11,wordAt a 61,wordAt a 62⟩

def stateFromWords (a : Array Nat) : Except Error State := do
  unless a.size ≥ 64 && wordAt a 0 == magic do throw .state
  let c := configFromWords a
  unless c.valid && a.size == contextWords c && wordAt a 12 ≤ c.history && wordAt a 27 ≤ c.ranges do throw .state
  let rangeBase := 64+32*c.paths+20*c.history
  let b : Batch := {phase := wordAt a 23, space := wordAt a 24, now := wordAt a 25, delay := wordAt a 26, cursor := wordAt a 28, largest := wordAt a 30, sampleTime := wordAt a 56, sampleNew := wordAt a 57 != 0, anyEliciting := wordAt a 58 != 0, rangeIndex := wordAt a 59, seen := wordAt a 60, anyNew := wordAt a 29 != 0, ranges := (List.range (wordAt a 27)).toArray.map (fun i => ⟨wordAt a (rangeBase+2*i),wordAt a (rangeBase+2*i+1)⟩)}
  return {config := c, generation := wordAt a 1, slot := wordAt a 2, nextAttempt := wordAt a 13, pending := wordAt a 14, live := wordAt a 15, now := wordAt a 16, server := wordAt a 17 != 0, complete := wordAt a 18 != 0, confirmed := wordAt a 19 != 0, peerValidated := wordAt a 20 != 0, activePath := wordAt a 21, ptoCount := wordAt a 22, keys := wordAt a 31, retired := wordAt a 63, batch := b, spaces := (List.range 3).toArray.map (fun i => Space.fromWords a (32+8*i)), paths := (List.range c.paths).toArray.map (fun i => Path.fromWords a (64+32*i)), packets := (List.range (wordAt a 12)).toArray.map (fun i => Packet.fromWords a (64+32*c.paths+20*i))}

def Action.words (a : Action) : Array Nat :=
  #[a.kind,a.index,a.pn,a.token,a.time,a.frames,a.frameGeneration,a.buffer]

end Libp2pAsm.Spec.Quic.Recovery
