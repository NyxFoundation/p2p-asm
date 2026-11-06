import Tests.CertificateAuth.Support

namespace Libp2pAsm.Tests.CertificateAuth
open Rv64

/-- Finite equal-public-input trace check, not a relational CT theorem.
Checks every fetched PC and memory event in both executions. -/
def tracePair (p : Program) (fa fb : Fixture) :
    Nat → State → State → Nat → Except String (Completed × Completed)
  | 0, _, _, _ => .error "trace instruction budget exhausted"
  | fuel+1, a, b, steps => do
    unless a.pc == b.pc do throw s!"PC trace differs at step {steps}"
    if a.pc == BitVec.ofNat 64 returnPC then return (⟨a,steps⟩,⟨b,steps⟩)
    let i ← (p.fetch a.pc).mapError reprStr
    unless access a i == access b i do throw s!"address trace differs at step {steps}"
    for (f,s) in [(fa,a),(fb,b)] do
      if let some (write,w,address) := access s i then
        unless allowed (if write then f.writes else f.reads) address w do
          throw s!"trace footprint at step {steps}"
    let nextA ← (execInstr i a).mapError reprStr
    let nextB ← (execInstr i b).mapError reprStr
    tracePair p fa fb fuel nextA nextB (steps+1)

end Libp2pAsm.Tests.CertificateAuth
