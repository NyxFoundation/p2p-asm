import Libp2pAsm.Refinement.AsmDer.EncodeCount
import Libp2pAsm.Rv64.Logic.ParserPatch

namespace Libp2pAsm.Refinement.AsmDer.Encode
open Rv64 Rv64.Logic Rv64.Logic.Parser
open Spec.Codec.Der (significantBytes)

theorem significant_eq_be (value : Nat) : beBytes (significantBytes value).length value=significantBytes value := by
  induction value using Nat.strongRecOn with
  | ind value ih =>
    by_cases hz : value=0
    · subst value; simp [significantBytes,beBytes]
    · have hdec : value/256<value := Nat.div_lt_self (by omega) (by decide)
      have hs : significantBytes value=significantBytes (value/256)++[value.toUInt8] := by
        rw [significantBytes,dif_neg hz]
      rw [hs,List.length_append,List.length_singleton,beBytes,ih _ hdec]

end Libp2pAsm.Refinement.AsmDer.Encode
