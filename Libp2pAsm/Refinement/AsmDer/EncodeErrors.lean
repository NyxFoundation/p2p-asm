import Libp2pAsm.Refinement.AsmDer.Programs
import Libp2pAsm.Rv64.Logic.ParserAccessExit

namespace Libp2pAsm.Refinement.AsmDer.Encode
open Rv64 Rv64.Logic Rv64.Logic.Parser
open Rv64.Logic.Parser.Wide (exitProgram)

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

def errorTable : Array (Nat × Fin 10) :=
  #[(2,6),(22,6),(41,6),(70,5),(92,4)]

def errorIndex (i : Fin 5) : Nat := errorTable[i].1
def errorStatus (i : Fin 5) : Fin 10 := errorTable[i].2
def errorPC (i : Fin 5) : Word := codeAddress encoder (errorIndex i)

theorem error_slice_checked (i : Fin 5) :
    CodeSlice encoder (relocated (exitProgram (errorStatus i)) (errorPC i)) (errorIndex i) := by
  refine ⟨by decide +revert,by decide +revert,?_⟩
  have h : ∀ i : Fin 5, ∀ j : Fin 16,
      encoder.code[errorIndex i+j.val]'(by have := i.isLt; have := j.isLt; decide +revert) =
        (exitProgram (errorStatus i)).code[j.val]'(by decide +revert) := by decide
  intro j hj
  have hs : (relocated (exitProgram (errorStatus i)) (errorPC i)).code.size=16 := by decide +revert
  exact h i ⟨j,by omega⟩

theorem error_return (i : Fin 5) (s : State) (hra : s.getReg .x1=0) :
    ∃ t, AccessTrace encoder 0 [] [] 16 (atPC s (errorPC i)) t ∧ t.pc=0 ∧
      ErrorOutput (errorStatus i).val t ∧ WriteTrace encoder 0 0 0 16 (atPC s (errorPC i)) t := by
  exact Wide.error_slice encoder (errorPC i) (errorIndex i) (errorStatus i) s (error_slice_checked i)
    ⟨by decide +revert,by decide +revert,by decide,by decide +revert⟩
    (by decide) (by decide) hra

end Libp2pAsm.Refinement.AsmDer.Encode
