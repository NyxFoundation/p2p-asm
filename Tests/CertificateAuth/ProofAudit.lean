import Lean
import Libp2pAsm.Refinement.Identity.Certificate.Binding
import Libp2pAsm.Refinement.Identity.Certificate.Usage
import Libp2pAsm.Refinement.Identity.Certificate.Grammar

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, ci) in env.constants.toList do
    if ci.isTheorem && name.toString.startsWith "Libp2pAsm.Refinement.Identity.Certificate." then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do throwError "unapproved transitive axiom {ax} in {name}"
      count := count+1
      logInfo m!"AUDIT {name}: {axioms}"
  unless count ≥ 18 do throwError "unexpected certificate theorem count: {count}"
  logInfo m!"PASS transitive certificate axiom audit: {count} declarations"
