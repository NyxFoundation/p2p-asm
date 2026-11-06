import Libp2pAsm.Spec.Stream.Receive
import Libp2pAsm.Spec.Stream.Send

namespace Libp2pAsm.Spec.Stream

private def contiguous (bytes : List (Nat × UInt8)) : Nat → Nat → List UInt8
  | 0, _ => []
  | budget+1, pos => match bytes.find? (fun p => p.1 == pos) with
    | none => []
    | some (_,v) => v :: contiguous bytes budget (pos+1)

/-- Pure delivery is a byte sequence; it does not expose implementation pointers.
The implementation can split this sequence at the ring boundary. -/
def Receive.delivery (s : Receive) : List UInt8 :=
  if s.reset then [] else contiguous s.bytes s.capacity s.consumed

def Receive.eof (s : Receive) : Bool := !s.reset && s.finalSize == some s.consumed

private theorem contiguous_length (bytes : List (Nat × UInt8)) (n pos : Nat) :
    (contiguous bytes n pos).length ≤ n := by
  induction n generalizing pos with
  | zero => simp [contiguous]
  | succ n ih =>
    simp only [contiguous]
    split
    · simp
    · simp only [List.length_cons]
      have := ih (pos+1)
      omega

theorem delivery_bounded (s : Receive) : s.delivery.length ≤ s.capacity := by
  unfold Receive.delivery
  split
  · simp
  · exact contiguous_length _ _ _

/-- Immutable pending plaintext, suitable for fresh-PN repacketization. -/
def Send.borrow (s : Send) : Option (Range × List UInt8) :=
  s.pending.map fun r => (r,(s.data.drop (r.start-s.base)).take r.length)

theorem borrow_length_bounded (s : Send) (r : Range) (bytes : List UInt8)
    (h : s.borrow = some (r,bytes)) : bytes.length ≤ r.length := by
  unfold Send.borrow at h
  cases hp : s.pending with
  | none => simp [hp] at h
  | some p =>
    simp [hp] at h
    obtain ⟨rfl,rfl⟩ := h
    simp only [List.length_take, List.length_drop]
    omega

end Libp2pAsm.Spec.Stream
