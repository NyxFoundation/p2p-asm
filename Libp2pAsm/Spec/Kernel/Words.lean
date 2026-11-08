import Std

namespace Libp2pAsm.Spec.Kernel

def wordMax : Nat := 2^64-1

def pack (xs : List Nat) : List UInt8 := xs.flatMap fun n =>
  (List.range 8).map fun i => Nat.toUInt8 (n / 2^(8*i) % 256)

def word (bs : Array UInt8) (off : Nat) : Nat :=
  (List.range 8).foldl (fun n i => n + bs[off+i]!.toNat * 2^(8*i)) 0

def unpack (bs : Array UInt8) : List Nat :=
  (List.range (bs.size/8)).map fun i => word bs (i*8)

def fits (base size : Nat) : Prop := base + size ≤ wordMax

def disjoint (a n b m : Nat) : Prop := a+n ≤ b ∨ b+m ≤ a

instance (a n b m : Nat) : Decidable (disjoint a n b m) :=
  inferInstanceAs (Decidable (a+n ≤ b ∨ b+m ≤ a))

structure Result where
  status : Nat := 0
  first : Nat := 0
  second : Nat := 0
  state : List Nat
  deriving Repr, BEq

def fail (state : List Nat) (status : Nat) : Result := ⟨status,0,0,state⟩

end Libp2pAsm.Spec.Kernel
