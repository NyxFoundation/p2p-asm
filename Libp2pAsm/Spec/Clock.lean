import Libp2pAsm.Spec.Limits

namespace Libp2pAsm.Spec.Clock

/-- Samples must be correlated and ordered by the core before this policy is applied. -/
structure Sample where
  sourceStatus : Nat := 0
  beforeNs : Nat
  afterNs : Nat
  seconds : Int
  nanos : Nat
  deriving Repr, BEq

/-- Modes: 0=initial, 1=trusted, 2=unavailable, 3=stopped, 4=recovery candidate. -/
structure State where
  mode : Nat := 0
  afterNs : Nat := 0
  seconds : Int := 0
  nanos : Nat := 0
  deriving Repr, BEq

inductive Status where
  | trusted | wallUnavailable | monotonicFailure | invalidLimits | invalidState
  deriving Repr, BEq, DecidableEq

def Status.code : Status → Nat
  | .trusted => 0 | .wallUnavailable => 1 | .monotonicFailure => 2
  | .invalidLimits => 3 | .invalidState => 4

def State.valid (s : State) : Bool := decide (
  s.mode ≤ 4 ∧ s.afterNs < 2^64 ∧ -(2^63) ≤ s.seconds ∧ s.seconds < 2^63 ∧
  s.nanos < 2^64 ∧ ((s.mode = 1 ∨ s.mode = 4) → s.nanos < 1000000000))

private def anchor (sample : Sample) (mode : Nat) : State :=
  { mode, afterNs := sample.afterNs, seconds := sample.seconds, nanos := sample.nanos }

private def consistent (s : State) (sample : Sample) (drift : Nat) : Bool :=
  let elapsed := (sample.seconds - s.seconds) * 1000000000 +
    Int.ofNat sample.nanos - Int.ofNat s.nanos
  decide (0 ≤ elapsed ∧ (elapsed - Int.ofNat (sample.afterNs - s.afterNs)).natAbs ≤ drift)

/-- Initial wall time is an environment assumption. After a fault, two consecutive
    coherent readings are required; consistency never authenticates absolute UTC. -/
def update (s : State) (sample : Sample) (drift span : Nat) : Status × State :=
  if drift = 0 ∨ drift ≥ 2^64 ∨ span = 0 ∨ span > drift then (.invalidLimits, s)
  else if !s.valid then (.invalidState, s)
  else if s.mode = 3 then (.monotonicFailure, s)
  else if sample.sourceStatus ≥ 2 ∨ sample.beforeNs ≥ 2^64 ∨ sample.afterNs ≥ 2^64 ∨
      sample.afterNs < sample.beforeNs ∨ (s.mode ≠ 0 ∧ sample.beforeNs < s.afterNs) then
    (.monotonicFailure, { s with mode := 3, seconds := 0, nanos := 0 })
  else if sample.sourceStatus = 1 ∨ sample.afterNs - sample.beforeNs > span ∨
      sample.nanos ≥ 1000000000 ∨ sample.seconds < -(2^63) ∨ sample.seconds ≥ 2^63 then
    (.wallUnavailable, { mode := 2, afterNs := sample.afterNs })
  else if s.mode = 2 then (.wallUnavailable, anchor sample 4)
  else if s.mode = 0 ∨ consistent s sample drift then (.trusted, anchor sample 1)
  else (.wallUnavailable, anchor sample 4)

end Libp2pAsm.Spec.Clock
