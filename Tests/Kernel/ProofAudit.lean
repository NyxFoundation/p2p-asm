import Lean
import Libp2pAsm.Refinement.Kernel.Invariants
import Libp2pAsm.Refinement.Kernel.Machine

open Lean Elab Command
elab "audit_kernel_axioms" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name,info) in env.constants.toList do
    if (`Libp2pAsm.Refinement.Kernel).isPrefixOf name && info.isTheorem then
      elabCommand (← `(#print axioms $(mkIdent name)))
      count := count+1
  logInfo m!"KERNEL_THEOREMS={count}"
audit_kernel_axioms
