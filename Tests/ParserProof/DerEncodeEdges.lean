import Tests.ParserProof.DerEncode

namespace Libp2pAsm.Tests.ParserProof.DerEncode
open Rv64 Rv64.Logic Rv64.Logic.Parser Refinement.AsmDer Refinement.AsmDer.Encode

set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def errorCases : Array (Word × Word × Word × Word × Spec.Codec.Der.Error) :=
  #[(256,0,18446744073709551615,0,.unsupportedTag),
    (31,0,18446744073709551615,0,.unsupportedTag),
    (0,0,18446744073709551615,0,.unsupportedTag),
    (4,0,18446744073709551615,1,.capacity),
    (4,0,18446744073709551615,2,.range)]

theorem every_error_returns (i : Fin 5) :
    let c := errorCases[i]
    ∃ done, runUntil image 524288 157 (metadata c.1 c.2.1 c.2.2.1 c.2.2.2.1)=.ok done ∧
      ErrorOutput c.2.2.2.2.code done.state ∧
      AccessTrace image 524288 [] [] done.steps (metadata c.1 c.2.1 c.2.2.1 c.2.2.2.1) done.state ∧
      done.state.memory=(metadata c.1 c.2.1 c.2.2.1 c.2.2.2.1).memory := by
  apply rejected_without_mapping
  decide +revert

def topOutput : State := entry 4 0 18446744073709551614 2
  (heap 18446744073709551614 #[0xcc,0xcc] true [])

theorem top_output_returns : ∃ done, runUntil image 524288 157 topOutput=.ok done ∧
    done.state.getReg .x11=2 ∧ done.state.memory=heap 18446744073709551614 #[4,0] true [] ∧
    AccessTrace image 524288 [] [(1,18446744073709551614),(1,18446744073709551615)]
      done.steps topOutput done.state := by
  have hv := invocation topOutput (by cbv)
    (by intro r hr _; simp [topOutput,entry,heap] at hr; subst r; right; decide) rfl
  have hi : InputAt topOutput #[0xcc,0xcc] [] := by
    intro _; exact ⟨rfl,by decide,by decide⟩
  obtain ⟨done,hr,ho,hm,ht,_⟩ := encode_embedded image 524292 1 topOutput #[0xcc,0xcc] [] hv rfl hi
  exact ⟨done,hr.run,ho.1,hm,ht⟩

end Libp2pAsm.Tests.ParserProof.DerEncode
