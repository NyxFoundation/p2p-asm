import Libp2pAsm.Rv64.Logic.Symbolic
import Lean.Elab.Term
import Lean.Elab.Tactic.Unfold

open Lean Elab Term in
/-- Refer to a frozen private definition by its source name, without copying its body. -/
elab "parser_internal% " id:ident : term => do
  let env ← getEnv
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
      privateToUserName name == id.getId)
    | throwError "Implementation constant {id.getId} is absent"
  return mkConst name

open Lean Elab Tactic in
elab "parser_unfold " id:ident " at " h:ident : tactic => do
  let env ← getEnv
  let some (name, _) := env.constants.toList.find? (fun (name, _) =>
      privateToUserName name == id.getId)
    | throwError "Implementation constant {id.getId} is absent"
  unfoldLocalDecl name (← getFVarId h)

open Libp2pAsm.Rv64 Libp2pAsm.Rv64.Logic in
/-- Symbolic instruction execution; concrete fetch is reduced by the kernel. -/
macro "parser_step" : tactic => `(tactic| (
  apply Trace.cons
  · simp [advance_eq_atPC]
  · apply step_of_fetch
    · simp only [advance_eq_atPC, pc_atPC, State.pc_setReg]
      conv => lhs; cbv
      try rfl
    · simp [execInstr, loadReg, storeReg_eq_atPC, bind, Except.bind, pure, Except.pure,
        writeReg, branch, jump_eq_atPC, advance_eq_atPC, getReg_setReg, *]
      <;> (try simp_all) <;> first | rfl | (split <;> first | omega | rfl)))
