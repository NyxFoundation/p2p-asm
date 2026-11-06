import Std

namespace Libp2pAsm.Spec.Abi

structure RegisteredRegion where
  generation : Nat
  base : Nat
  capacity : Nat
  active : Bool
  writable : Bool
  deriving Repr

structure BufferRef where
  slot : Nat
  generation : Nat
  offset : Nat
  length : Nat
  deriving Repr

structure Span where
  address : Nat
  length : Nat
  deriving Repr, BEq, DecidableEq

inductive BufferError where
  | unknownRegion | staleRegion | bounds | invalidRegion | readOnly
  deriving Repr, BEq, DecidableEq

def BufferError.code : BufferError → Nat
  | .unknownRegion => 1 | .staleRegion => 2 | .bounds => 3
  | .invalidRegion => 4 | .readOnly => 5

/-- Even the one-past-end address must be representable; empty end views cannot wrap. -/
def RegisteredRegion.valid (r : RegisteredRegion) : Prop :=
  0 < r.capacity ∧ r.generation < 2^64 ∧ r.base + r.capacity < 2^64

instance (r : RegisteredRegion) : Decidable r.valid :=
  inferInstanceAs (Decidable (0 < r.capacity ∧ r.generation < 2^64 ∧ r.base + r.capacity < 2^64))

def resolveBuffer (regions : Array RegisteredRegion) (ref : BufferRef) (write : Bool) :
    Except BufferError Span :=
  match regions[ref.slot]? with
  | none => .error .unknownRegion
  | some r =>
    if r.active ≠ true then .error .staleRegion
    else if ref.generation ≠ r.generation then .error .staleRegion
    else if ¬r.valid then .error .invalidRegion
    else if write = true ∧ r.writable ≠ true then .error .readOnly
    else if r.capacity < ref.length then .error .bounds
    else if r.capacity - ref.length < ref.offset then .error .bounds
    else .ok ⟨r.base + ref.offset, ref.length⟩

end Libp2pAsm.Spec.Abi
