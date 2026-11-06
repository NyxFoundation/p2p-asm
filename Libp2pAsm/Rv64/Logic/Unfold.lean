import Lean.Elab.Tactic.Unfold

open Lean Elab Tactic in
/-- Unfold a private implementation constant already present in the goal.
This only performs kernel definitional reduction; it adds no logical assumptions. -/
elab "unfold_internal " id:ident : tactic => do
  let target ← getMainTarget
  let some name := target.getUsedConstants.find? (fun name =>
      privateToUserName name == id.getId)
    | throwError "Implementation constant {id.getId} is absent from the goal"
  unfoldTarget name
