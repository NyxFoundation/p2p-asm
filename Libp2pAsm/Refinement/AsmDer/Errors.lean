import Libp2pAsm.Refinement.AsmDer.Programs
import Libp2pAsm.Rv64.Logic.ParserExit

namespace Libp2pAsm.Refinement.AsmDer
open Rv64 Rv64.Logic Rv64.Logic.Parser

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

def errorTable : Array (Nat × Fin 9) :=
  #[(5,4),(24,1),(44,6),(64,6),(83,6),(102,1),(127,7),
    (146,8),(166,2),(184,1),(203,3),(232,3),(251,1)]

def errorIndex (i : Fin 13) : Nat := errorTable[i].1
def errorStatus (i : Fin 13) : Fin 9 := errorTable[i].2
def errorPC (i : Fin 13) : Word := codeAddress decoder (errorIndex i)

theorem error_slice_checked (i : Fin 13) :
    CodeSlice decoder (relocated (exitProgram (errorStatus i)) (errorPC i)) (errorIndex i) := by
  refine ⟨by decide +revert,by decide +revert,?_⟩
  have h : ∀ i : Fin 13, ∀ j : Fin 16,
      decoder.code[errorIndex i+j.val]'(by have := i.isLt; have := j.isLt; decide +revert) =
        (exitProgram (errorStatus i)).code[j.val]'(by decide +revert) := by decide
  intro j hj
  have hs : (relocated (exitProgram (errorStatus i)) (errorPC i)).code.size=16 := by decide +revert
  exact h i ⟨j,by omega⟩

theorem error_return (i : Fin 13) (s : State) (hra : s.getReg .x1=0) :
    ∃ t, ReadTrace decoder 0 [] 16 (atPC s (errorPC i)) t ∧ t.pc=0 ∧
      ErrorOutput (errorStatus i).val t ∧ WriteTrace decoder 0 0 0 16 (atPC s (errorPC i)) t := by
  exact error_slice decoder (errorPC i) (errorIndex i) (errorStatus i) s (error_slice_checked i)
    ⟨by decide +revert,by decide +revert,by decide,by decide +revert⟩
    (by decide) (by decide) hra

theorem error_post (s : State) (e : Spec.Codec.Der.Error) (h : ErrorOutput e.code s) :
    DecodePost (.error e) s := by
  exact ⟨h.1,h.2 .x11 (by simp [Asm.Crypto.Sha2.cleared]) (by decide),h.2 .x12 (by simp [Asm.Crypto.Sha2.cleared]) (by decide),
    h.2 .x13 (by simp [Asm.Crypto.Sha2.cleared]) (by decide),h.2 .x14 (by simp [Asm.Crypto.Sha2.cleared]) (by decide)⟩

end Libp2pAsm.Refinement.AsmDer
