import Libp2pAsm.Refinement.Identity.PeerProgram
import Libp2pAsm.Rv64.Logic.ParserAccessExit

namespace Libp2pAsm.Refinement.Identity.Peer
open Rv64 Rv64.Logic Rv64.Logic.Parser
open Rv64.Logic.Parser.Wide (exitProgram)

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

def errorTable : Array (Nat × Fin 10) :=
  #[(4,8),(24,9),(43,5),(65,4),(88,4),(113,4),(133,4)]

def errorIndex (i : Fin 7) : Nat := errorTable[i].1
def errorStatus (i : Fin 7) : Fin 10 := errorTable[i].2
def errorPC (i : Fin 7) : Word := codeAddress program (errorIndex i)

theorem error_slice_checked (i : Fin 7) :
    CodeSlice program (relocated (exitProgram (errorStatus i)) (errorPC i)) (errorIndex i) := by
  refine ⟨by decide +revert,by decide +revert,?_⟩
  have h : ∀ i : Fin 7, ∀ j : Fin 16,
      program.code[errorIndex i+j.val]'(by have := i.isLt; have := j.isLt; decide +revert) =
        (exitProgram (errorStatus i)).code[j.val]'(by decide +revert) := by decide
  intro j hj
  have hs : (relocated (exitProgram (errorStatus i)) (errorPC i)).code.size=16 := by decide +revert
  exact h i ⟨j,by omega⟩

theorem error_return (i : Fin 7) (s : State) (hra : s.getReg .x1=0) :
    ∃ t, AccessTrace program 0 [] [] 16 (atPC s (errorPC i)) t ∧ t.pc=0 ∧
      ErrorOutput (errorStatus i).val t ∧ WriteTrace program 0 0 0 16 (atPC s (errorPC i)) t := by
  exact Wide.error_slice program (errorPC i) (errorIndex i) (errorStatus i) s (error_slice_checked i)
    ⟨by decide +revert,by decide +revert,by decide,by decide +revert⟩
    (by decide) (by decide) hra

end Libp2pAsm.Refinement.Identity.Peer
