import Libp2pAsm.Spec.Multistream.Negotiation

namespace Libp2pAsm.Spec.Multistream

def timer (s : State) (now : Nat) : State :=
  if s.phase = .selected ∨ s.phase = .closed ∨ now < s.deadline then s
  else {s with phase := .closed, pending := []}

theorem selected_timer_noop (s : State) (now : Nat) (h : s.phase = .selected) : timer s now = s := by
  simp [timer,h]

/-- Framing arbitrary configured-length proposals uses the frozen canonical codec.
The runtime only advertises the three fixed, short messages in Framing.lean. -/
def encodeFrame (text : List UInt8) : Except Codec.Error (List UInt8) := do
  let length ← Codec.UnsignedVarint.encode text.length
  return length ++ text

theorem canonical_header : encodeFrame header = .ok (frame header) := by rfl

theorem canonical_ping : encodeFrame ping = .ok (frame ping) := by rfl

end Libp2pAsm.Spec.Multistream
