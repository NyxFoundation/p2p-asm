import Libp2pAsm.Spec.Ping.Protocol

namespace Libp2pAsm.Spec.Ping

def finish (s : State) : Except Error State := do
  unless s.authenticated && s.handshakeConfirmed do throw .gate
  unless s.outbound || s.phase ≠ 2 do throw .backpressure
  unless s.phase ≠ 3 do throw .closed
  return {s with localFin := true}

def Quota.release (q : Quota) (outbound : Bool) : Option Quota :=
  if outbound then if 0 < q.outbound then some {q with outbound := q.outbound-1} else none
  else if 0 < q.inbound then some {q with inbound := q.inbound-1} else none

theorem quota_release_underflow : ({} : Quota).release true = none ∧
    ({} : Quota).release false = none := by constructor <;> rfl

theorem timer_preserves_closed (s : State) (now : Nat) (h : s.phase = 3) : timer s now = s := by
  simp [timer,h]

theorem timer_wipes_on_expiry (s : State) (now : Nat) (h : s.phase ≠ 3) (ht : s.deadline ≤ now) :
    (timer s now).received = [] ∧ (timer s now).expected = [] := by
  simp [timer,h, Nat.not_lt.mpr ht,cancel]

end Libp2pAsm.Spec.Ping
