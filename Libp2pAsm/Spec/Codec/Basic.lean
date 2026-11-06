import Std

namespace Libp2pAsm.Spec.Codec

inductive Error where
  | truncated | overflow | nonMinimal
  deriving DecidableEq, BEq, Repr

structure Decoded where
  value : Nat
  consumed : Nat
  deriving DecidableEq, BEq, Repr

end Libp2pAsm.Spec.Codec
