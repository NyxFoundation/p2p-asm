import Lean
import Libp2pAsm.Refinement.Stream.Arithmetic
import Libp2pAsm.Refinement.Stream.Framing
import Libp2pAsm.Refinement.Stream.IdTrace
import Libp2pAsm.Spec.Multistream.Negotiation
import Libp2pAsm.Spec.Ping.Lifecycle
import Libp2pAsm.Spec.Stream.Delivery
import Libp2pAsm.Spec.Multistream.Lifecycle

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let prefixes := ["Libp2pAsm.Spec.Stream.", "Libp2pAsm.Spec.Multistream.",
    "Libp2pAsm.Spec.Ping.", "Libp2pAsm.Refinement.Stream."]
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, ci) in env.constants.toList do
    if ci.isTheorem && prefixes.any (fun p => name.toString.startsWith p) then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "unapproved transitive axiom {ax} in {name}"
      count := count+1
      logInfo m!"AUDIT {name}: {axioms}"
  unless count ≥ 20 do throwError "unexpected theorem audit count: {count}"
  logInfo m!"PASS automatic transitive axiom audit: {count} declarations"
