import Libp2pAsm.Spec.Stream.Receive

namespace Libp2pAsm.Spec.Stream

structure Range where
  start : Nat
  length : Nat
  fin : Bool := false
  deriving DecidableEq, Repr

def Range.endPos (r : Range) : Nat := r.start+r.length

structure Send where
  capacity : Nat
  base : Nat := 0
  queued : Nat := 0
  sent : Nat := 0
  limit : Nat := maxOffset
  allowance : Nat := maxOffset
  finalSize : Option Nat := none
  finSent : Bool := false
  finAck : Bool := false
  reset : Bool := false
  pending : Option Range := none
  data : List UInt8 := []
  acked : List Nat := []
  deriving DecidableEq, Repr

def Send.append (s : Send) (input : List UInt8) (fin : Bool) : Except Error Send := do
  unless !s.reset && s.finalSize.isNone do throw .unavailable
  let endPos := s.queued+input.length
  unless endPos ≤ maxOffset do throw .offset
  unless endPos-s.base ≤ s.capacity do throw .buffer
  return {s with
    queued := endPos, data := s.data ++ input
    finalSize := if fin then some endPos else none}

def Send.reserve (s : Send) (r : Range) : Except Error (Send × Nat) := do
  unless !s.reset && s.pending.isNone do throw .unavailable
  unless s.base ≤ r.start ∧ r.start ≤ s.sent ∧ r.endPos ≤ s.queued do throw .unavailable
  unless !r.fin || s.finalSize = some r.endPos do throw .finalSize
  let delta := creditDelta s.sent r.endPos
  unless r.endPos ≤ s.limit ∧ delta ≤ s.allowance do throw .flow
  return ({s with pending := some r}, delta)

private def collectCount (acked : List Nat) (stop : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel+1, pos => if pos < stop && acked.contains pos then
      1+collectCount acked stop fuel (pos+1) else 0

def Send.collect (s : Send) : Send :=
  let stop := match s.pending with | none => s.sent | some r => min s.sent r.start
  let n := collectCount s.acked stop s.capacity s.base
  {s with
    base := s.base+n, data := s.data.drop n,
    acked := s.acked.filter (fun p => s.base+n ≤ p)}

def Send.settle (s : Send) (success : Bool) : Except Error (Send × Nat) := do
  let some r := s.pending | throw .unavailable
  let delta := creditDelta s.sent r.endPos
  let t := {s with
    pending := none, sent := if success then max s.sent r.endPos else s.sent
    finSent := s.finSent || (success && r.fin)}
  return (t.collect, delta)

def Send.acknowledge (s : Send) (r : Range) : Except Error Send := do
  unless r.endPos ≤ s.sent do throw .unavailable
  unless !r.fin || (s.finSent && s.finalSize == some r.endPos) do throw .finalSize
  let positions := (List.range r.length).map (r.start+·)
  return ({s with
    acked := (s.acked ++ positions).filter (s.base ≤ ·)
    finAck := s.finAck || r.fin} : Send).collect

def Send.stop (s : Send) : Except Error Send := do
  unless s.pending.isNone do throw .unavailable
  return {s with
    base := s.sent, queued := s.sent, finalSize := some s.sent
    data := [], acked := [], reset := true}

theorem retransmission_zero_credit (sent : Nat) (r : Range) (h : r.endPos ≤ sent) :
    creditDelta sent r.endPos = 0 := credit_duplicate _ _ h

theorem reservation_bounds (base sent queued start len : Nat)
    (h : base ≤ start ∧ start ≤ sent ∧ start+len ≤ queued) :
    base ≤ start ∧ start+len ≤ queued ∧ max sent (start+len)-sent ≤ queued-sent := by omega

theorem send_cancel_preserves_sent (s : Send) (r : Range) (h : s.pending = some r) :
    (s.settle false).map (fun p => p.1.sent) = .ok s.sent := by
  simp [Send.settle, h, Send.collect]
  rfl

end Libp2pAsm.Spec.Stream
