import Libp2pAsm.Spec.Stream.Receive

namespace Libp2pAsm.Spec.Stream

structure IdParts where
  initiator : Nat
  unidirectional : Nat
  ordinal : Nat
  localInitiated : Bool
  deriving DecidableEq, Repr

def classifyId (id role count direction : Nat) : Option IdParts := do
  if role > 1 || direction > 1 || id > maxOffset || count > 2^60 then none else do
    let localInit := id%2 = role
    if id/4 ≥ count || (id/2%2 = 1 && localInit != (direction = 1)) then none else
      some ⟨id%2,id/2%2,id/4,localInit⟩

theorem id_ordinal_bound (id : Nat) (h : id ≤ maxOffset) : id/4 < 2^60 := by
  unfold maxOffset at h
  omega

theorem id_parts_reconstruct (id : Nat) : (id/4)*4+(id/2%2)*2+id%2 = id := by omega

end Libp2pAsm.Spec.Stream
