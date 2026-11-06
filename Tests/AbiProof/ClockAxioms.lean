import Tests.AbiProof.ClockEarly
import Tests.AbiProof.ClockUpdate
import Libp2pAsm.Rv64.Logic.WordHeap
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let env ← Lean.getEnv
  let roots := [`Libp2pAsm.Rv64.Logic, `Libp2pAsm.Refinement.Clock, `Libp2pAsm.Tests.AbiProof]
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for (name, info) in env.constants.toList do
    if roots.any (·.isPrefixOf name) && info.isTheorem then
      for dependency in ← Lean.collectAxioms name do
        unless allowed.contains dependency do
          throwError "Unexpected dependency in {name}: {dependency}"

#print axioms Libp2pAsm.Refinement.Clock.invalid_limits_embedded
#print axioms Libp2pAsm.Refinement.Clock.invalid_state_embedded
#print axioms Libp2pAsm.Refinement.Clock.stopped_embedded
#print axioms Libp2pAsm.Rv64.Logic.readLE64_writeLE64
#print axioms Libp2pAsm.Refinement.Clock.multiply_with_carry
#print axioms Libp2pAsm.Refinement.Clock.withinDrift_exact
#print axioms Libp2pAsm.Refinement.Clock.raw_refines_spec
#print axioms Libp2pAsm.Refinement.Clock.check_embedded

