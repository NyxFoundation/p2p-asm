import Tests.AbiProof.Buffer
import Lean.Util.CollectAxioms
import Lean.Elab.Command

-- Audit every theorem in the ABI proof package and its dependency closure.
run_cmd do
  let env ← Lean.getEnv
  let roots := [`Libp2pAsm.Rv64.Logic, `Libp2pAsm.Refinement.AsmBuffer,
    `Libp2pAsm.Refinement.Clock, `Libp2pAsm.Tests.AbiProof]
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for (name, info) in env.constants.toList do
    if roots.any (·.isPrefixOf name) && info.isTheorem then
      for dependency in ← Lean.collectAxioms name do
        unless allowed.contains dependency do
          throwError "Unexpected dependency in {name}: {dependency}"

#print axioms Libp2pAsm.Refinement.AsmBuffer.raw_trace
#print axioms Libp2pAsm.Refinement.AsmBuffer.raw_refines_spec
#print axioms Libp2pAsm.Refinement.AsmBuffer.resolve_table_embedded
#print axioms Libp2pAsm.Refinement.AsmBuffer.invalid_access
#print axioms Libp2pAsm.Refinement.AsmBuffer.invalid_count
#print axioms Libp2pAsm.Tests.AbiProof.buffer_owned_span
