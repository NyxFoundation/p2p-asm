import Std

namespace Libp2pAsm.Spec.Stream

def maxOffset : Nat := 2^62-1

inductive Error where
  | metadata | offset | flow | finalSize | conflict | buffer | cryptoBuffer | unavailable
  deriving DecidableEq, Repr

/-- Absolute positions, independent of the implementation's ring representation. -/
structure Receive where
  capacity : Nat
  consumed : Nat := 0
  highest : Nat := 0
  finalSize : Option Nat := none
  limit : Nat := maxOffset
  allowance : Nat := maxOffset
  crypto : Bool := false
  reset : Bool := false
  bytes : List (Nat × UInt8) := []
  deriving DecidableEq, Repr

inductive ReceiveKind where
  | data | fin | reset
  deriving DecidableEq, Repr

def Receive.valid (s : Receive) : Prop :=
  0 < s.capacity ∧ s.capacity ≤ maxOffset ∧ s.consumed ≤ s.highest ∧
  s.highest ≤ maxOffset ∧ s.limit ≤ maxOffset ∧ s.allowance ≤ maxOffset ∧
  (∀ f ∈ s.finalSize, s.highest ≤ f ∧ f ≤ maxOffset) ∧
  (s.reset = true → s.finalSize ≠ none) ∧
  (∀ p ∈ s.bytes, s.consumed ≤ p.1 ∧ p.1 < s.consumed+s.capacity)

private def newBytes (s : Receive) (off : Nat) (input : List UInt8) : List (Nat × UInt8) :=
  (input.zipIdx.map fun (v,i) => (off+i,v)).filter (fun p => s.consumed ≤ p.1)

/-- Errors are values; no state is published on failure. The caller commits the
returned state and delta together with aggregate connection credit. -/
def Receive.put (s : Receive) (off : Nat) (input : List UInt8) (kind : ReceiveKind) :
    Except Error (Receive × Nat) := do
  let endPos := off+input.length
  unless !s.crypto || kind = .data do throw .metadata
  unless kind ≠ .reset || input.isEmpty do throw .metadata
  unless endPos ≤ maxOffset do throw .offset
  if let some final := s.finalSize then
    unless endPos ≤ final ∧ (kind = .data ∨ endPos = final) do throw .finalSize
  unless kind = .data ∨ s.highest ≤ endPos do throw .finalSize
  let delta := max s.highest endPos - s.highest
  unless s.crypto || (endPos ≤ s.limit ∧ delta ≤ s.allowance) do throw .flow
  let incoming := newBytes s off input
  unless kind = .reset || s.reset || incoming.isEmpty || endPos ≤ s.consumed+s.capacity do
    throw (if s.crypto then .cryptoBuffer else .buffer)
  unless s.reset || incoming.all (fun p => s.bytes.all fun q => q.1 != p.1 || q.2 == p.2) do
    throw .conflict
  let bytes := if kind = .reset then [] else if s.reset then s.bytes else
    s.bytes.filter (fun p => !incoming.any (fun q => p.1 == q.1)) ++ incoming
  return ({s with
    highest := max s.highest endPos,
    finalSize := if kind = .data then s.finalSize else some endPos,
    reset := s.reset || kind = .reset, bytes}, if s.crypto then 0 else delta)

def Receive.consume (s : Receive) (n : Nat) : Except Error Receive := do
  unless n ≤ s.capacity ∧ s.consumed+n ≤ s.highest do throw .unavailable
  unless (List.range n).all (fun i => s.bytes.any (fun p => p.1 == s.consumed+i)) do
    throw .unavailable
  return {s with
    consumed := s.consumed+n,
    bytes := s.bytes.filter (fun p => s.consumed+n ≤ p.1)}

def creditDelta (old endPos : Nat) : Nat := max old endPos - old

theorem credit_conservation (old endPos : Nat) :
    old + creditDelta old endPos = max old endPos := by
  unfold creditDelta
  omega

theorem credit_duplicate (old endPos : Nat) (h : endPos ≤ old) :
    creditDelta old endPos = 0 := by simp [creditDelta, Nat.max_eq_left h]

theorem credit_telescopes (a b c : Nat) :
    creditDelta a b + creditDelta (max a b) c = creditDelta a (max b c) := by
  unfold creditDelta
  omega

theorem checked_offset_addition (off len : Nat)
    (ho : off ≤ maxOffset) (hl : len ≤ maxOffset-off) : off+len ≤ maxOffset := by omega

theorem ring_index_bounded (off cap : Nat) (h : 0 < cap) : off % cap < cap :=
  Nat.mod_lt off h

theorem ring_slot_unique (a b base cap : Nat) (ha : base ≤ a) (hb : base ≤ b)
    (ha' : a < base+cap) (hb' : b < base+cap) (h : a % cap = b % cap) : a = b := by
  have qa := Nat.mod_add_div a cap
  have qb := Nat.mod_add_div b cap
  by_cases hq : a / cap < b / cap
  · have hm := Nat.mul_le_mul_left cap (Nat.succ_le_iff.mpr hq)
    simp only [Nat.mul_succ] at hm
    omega
  by_cases hq' : b / cap < a / cap
  · have hm := Nat.mul_le_mul_left cap (Nat.succ_le_iff.mpr hq')
    simp only [Nat.mul_succ] at hm
    omega
  have he : a / cap = b / cap := by omega
  rw [he] at qa
  omega

end Libp2pAsm.Spec.Stream
