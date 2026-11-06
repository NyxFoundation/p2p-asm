import Lean
import Libp2pAsm.Refinement.Quic.Wire.Machine
import Libp2pAsm.Refinement.Quic.Wire.Permission

open Lean Elab Command

elab "audit_wire_axioms" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  for (name,info) in env.constants.toList do
    if (`Libp2pAsm.Refinement.Quic.Wire).isPrefixOf name && info.isTheorem then
      elabCommand (← `(#print axioms $(mkIdent name)))
      count := count+1
  logInfo m!"WIRE_THEOREMS={count}"

audit_wire_axioms
