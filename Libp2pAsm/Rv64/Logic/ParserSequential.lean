import Libp2pAsm.Refinement.AsmProtobuf.ReadBounds

namespace Libp2pAsm.Rv64.Logic.Parser
open Refinement.AsmProtobuf.Footprint

theorem byteReads_add (ptr : Word) (n m : Nat) :
    byteReads ptr (n+m)=byteReads ptr n++byteReads (ptr+BitVec.ofNat 64 n) m := by
  induction n generalizing ptr with
  | zero => simp [byteReads]
  | succ n ih =>
    rw [Nat.succ_add,byteReads,ih,byteReads,List.cons_append]
    have hp : ptr+1+BitVec.ofNat 64 n=ptr+BitVec.ofNat 64 (n+1) := by
      rw [BitVec.ofNat_add,BitVec.add_assoc,BitVec.add_comm (1 : Word) (BitVec.ofNat 64 n)]
      rfl
    rw [hp]

end Libp2pAsm.Rv64.Logic.Parser
