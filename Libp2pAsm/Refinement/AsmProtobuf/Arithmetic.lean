import Libp2pAsm.Refinement.AsmCodec.UnsignedArithmetic

namespace Libp2pAsm.Refinement.AsmProtobuf
open Rv64 Rv64.Logic AsmCodec

theorem accumulate (acc count : Nat) (b : UInt8) (hc : count ≤ 9)
    (ha : acc < 2^(7*count)) :
    (BitVec.ofNat 64 acc ||| ((BitVec.ofNat 64 b.toNat &&& (127 : Word)) <<<
      ((BitVec.ofNat 64 (7*count)).toNat % 64))) =
        BitVec.ofNat 64 (acc + b.toNat % 128 * 2^(7*count)) := by
  have hs : 7*count < 64 := by omega
  have hs64 : 7*count < 2^64 := by omega
  rw [unsigned_payload_word]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs64, Nat.mod_eq_of_lt hs]
  rw [word_shift_ofNat, ← BitVec.ofNat_or, Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.add_comm]

end Libp2pAsm.Refinement.AsmProtobuf
