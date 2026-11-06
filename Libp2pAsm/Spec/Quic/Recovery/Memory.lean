import Libp2pAsm.Spec.Quic.Recovery.Raw

namespace Libp2pAsm.Spec.Quic.Recovery

structure Span where
  base : Nat
  size : Nat

def Span.valid (s : Span) : Bool := s.size == 0 || s.base+s.size ≤ wordLimit
def Span.apart (a b : Span) : Bool :=
  a.size == 0 || b.size == 0 || a.base+a.size ≤ b.base || b.base+b.size ≤ a.base

/-- Raw address/alignment checks are independent of authenticated input semantics.
Mapping, permissions, code separation, exclusive ownership and immutable input
remain caller preconditions, as for every existing machine-model leaf. -/
def validateAbi (descriptor stack : Nat) (d : Array Nat) : Except Error Unit := do
  unless descriptor % 8 == 0 && descriptor+64 ≤ wordLimit do throw .memory
  let v := wordAt d
  unless [v 0,v 2,v 4,v 6].all (fun p => p % 8 == 0) do throw .memory
  unless v 1 % 8 == 0 do throw .memory
  unless 512 ≤ v 1 do throw .capacity
  unless v 1 ≤ wordLimit-65 do throw .memory
  unless 128 ≤ v 3 && 64 ≤ v 5 && v 1+64 ≤ v 7 do throw .capacity
  unless stack % 16 == 0 do throw .memory
  let spans : List Span := [⟨descriptor,64⟩,⟨v 0,v 1⟩,⟨v 2,v 3⟩,⟨v 4,64⟩,⟨v 6,v 7⟩]
  unless spans.all Span.valid do throw .memory
  unless spans.zipIdx.all (fun (a,i) => (spans.drop (i+1)).all (Span.apart a)) do throw .memory

end Libp2pAsm.Spec.Quic.Recovery
