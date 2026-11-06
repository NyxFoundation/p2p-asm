import Std

namespace Libp2pAsm.Spec.Ping

inductive Error where
  | metadata | closed | backpressure | timeout | gate | mismatch | partialFin
  deriving DecidableEq, Repr

structure State where
  outbound : Bool
  phase : Nat := 0
  received : List UInt8 := []
  expected : List UInt8 := []
  deadline : Nat
  authenticated : Bool := false
  handshakeConfirmed : Bool := false
  localFin : Bool := false
  remoteFin : Bool := false
  entropyToken : Nat
  deriving DecidableEq, Repr

structure Result where
  state : State
  consumed : Nat := 0
  echo : List UInt8 := []
  matched : Bool := false
  closeWrite : Bool := false
  deriving DecidableEq, Repr

private def admission (s : State) (now : Nat) : Except Error Unit := do
  unless s.authenticated && s.handshakeConfirmed do throw .gate
  unless now < s.deadline do throw .timeout

def begin (s : State) (entropy : List UInt8) (token now : Nat) : Except Error State := do
  admission s now
  unless entropy.length = 32 ∧ token = s.entropyToken ∧ s.outbound do throw .metadata
  unless s.phase = 0 ∧ !s.localFin ∧ !s.remoteFin do throw .closed
  return {s with phase := 1, expected := entropy}

def feed (s : State) (input : List UInt8) (now : Nat) (fin : Bool) : Except Error Result := do
  admission s now
  unless s.phase ≠ 3 ∧ !s.remoteFin ∧ (s.outbound ∨ !s.localFin) do throw .closed
  unless s.phase ≠ 2 ∧ (!s.outbound ∨ s.phase = 1) do throw .backpressure
  let count := min input.length (32-s.received.length)
  let bytes := s.received ++ input.take count
  let ended := fin && count == input.length
  unless !ended ∨ bytes.length = 0 ∨ bytes.length = 32 do throw .partialFin
  unless bytes.length ≠ 32 ∨ !s.outbound ∨ bytes = s.expected do throw .mismatch
  unless !ended ∨ !bytes.isEmpty ∨ !s.outbound do throw .partialFin
  if ended && bytes.isEmpty then
    return ⟨{s with phase := 3, localFin := true, remoteFin := true},0,[],false,true⟩
  let ready := bytes.length == 32
  return {
    state := {s with
      received := bytes, phase := (if ready then 2 else s.phase), remoteFin := ended}
    consumed := count
    echo := if ready && !s.outbound then bytes else []
    matched := ready && s.outbound }

def release (s : State) (now : Nat) : Except Error State := do
  admission s now
  unless s.phase = 2 do throw .backpressure
  let closed := if s.outbound then s.localFin else s.remoteFin
  return {s with
    received := [], expected := [], phase := if closed then 3 else 0
    localFin := s.localFin || closed}

def cancel (s : State) : State :=
  {s with received := [], expected := [], phase := 3, localFin := true}

def timer (s : State) (now : Nat) : State :=
  if s.phase = 3 || now < s.deadline then s else cancel s

structure Quota where
  outbound : Nat := 0
  inbound : Nat := 0
  deriving DecidableEq, Repr

def Quota.acquire (q : Quota) (outbound : Bool) : Option Quota :=
  if outbound then if q.outbound < 1 then some {q with outbound := q.outbound+1} else none
  else if q.inbound < 2 then some {q with inbound := q.inbound+1} else none

theorem acquire_preserves_limits (q t : Quota) (outbound : Bool)
    (ho : q.outbound ≤ 1) (hi : q.inbound ≤ 2) (h : q.acquire outbound = some t) :
    t.outbound ≤ 1 ∧ t.inbound ≤ 2 := by
  cases outbound <;> simp [Quota.acquire] at h <;>
    obtain ⟨bound, rfl⟩ := h <;> simp_all <;> omega

theorem cancellation_wipes (s : State) :
    (cancel s).received = [] ∧ (cancel s).expected = [] ∧ (cancel s).phase = 3 := by
  simp [cancel]

theorem fragment_never_overfills (old input : List UInt8) (h : old.length ≤ 32) :
    (old ++ input.take (min input.length (32-old.length))).length ≤ 32 := by
  simp only [List.length_append, List.length_take]
  omega

end Libp2pAsm.Spec.Ping
