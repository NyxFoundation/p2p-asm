import Libp2pAsm.Spec.Crypto.Basic

namespace Libp2pAsm.Spec.Tls
abbrev Bytes := Array UInt8

/-- Numeric values are the public RV64 status ABI; no output on failure. -/
inductive Error where
  | needMore | malformed | unsupported | address | capacity | duplicate
  | profile | crypto | limit
  deriving BEq, DecidableEq, Repr

def Error.code : Error → Nat
  | .needMore => 1 | .malformed => 2 | .unsupported => 3
  | .address => 4 | .capacity => 5 | .duplicate => 6
  | .profile => 7 | .crypto => 8 | .limit => 9

structure Slice where
  offset : Nat
  length : Nat
  deriving BEq, DecidableEq, Repr, Inhabited

def Slice.valid (s : Slice) (size : Nat) : Prop := s.offset ≤ size ∧ s.length ≤ size-s.offset
def Slice.bytes (s : Slice) (input : Bytes) : Bytes := input.extract s.offset (s.offset+s.length)

def be (width n : Nat) : Bytes := (Crypto.Sha2.encodeBE width n).toArray

end Libp2pAsm.Spec.Tls
