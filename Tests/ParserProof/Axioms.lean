import Tests.ParserProof.Protobuf
import Tests.ParserProof.DerEdges
import Tests.ParserProof.DerEncodeEdges
import Libp2pAsm.Refinement.AsmProtobuf.ValueBounds
import Libp2pAsm.Refinement.Identity.Canonical
import Libp2pAsm.Rv64.Logic.ParserAccessExit
import Libp2pAsm.Refinement.Identity.View
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let env ← Lean.getEnv
  let roots := [`Libp2pAsm.Refinement.AsmProtobuf, `Libp2pAsm.Refinement.AsmDer,
    `Libp2pAsm.Refinement.Identity, `Libp2pAsm.Rv64.Logic.Parser, `Libp2pAsm.Tests.ParserProof]
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if roots.any (·.isPrefixOf name) && info.isTheorem then
      count := count+1
      for dependency in ← Lean.collectAxioms name do
        unless allowed.contains dependency do
          throwError "Unexpected dependency in {name}: {dependency}"
  Lean.logInfo m!"Audited {count} parser-proof theorems and all transitive axioms"

#print axioms Libp2pAsm.Refinement.AsmProtobuf.decode_with_footprint
#print axioms Libp2pAsm.Refinement.AsmDer.decode_with_footprint
#print axioms Libp2pAsm.Refinement.AsmDer.decode_reads_header
#print axioms Libp2pAsm.Refinement.AsmDer.Encode.encode_embedded
#print axioms Libp2pAsm.Refinement.Identity.fuel_irrelevant
#print axioms Libp2pAsm.Refinement.Identity.decode_view
#print axioms Libp2pAsm.Refinement.Identity.groups_fit
