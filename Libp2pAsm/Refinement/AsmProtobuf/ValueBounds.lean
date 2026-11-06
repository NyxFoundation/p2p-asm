import Libp2pAsm.Refinement.AsmProtobuf.Arithmetic
import Libp2pAsm.Refinement.AsmProtobuf.Specification

namespace Libp2pAsm.Refinement.AsmProtobuf
open Spec.Codec

theorem terminal_value_bound (acc index : Nat) (b : UInt8) (hi : index ≤ 9)
    (ha : acc < 2^(7*index)) (hg : index=9 → b.toNat ≤ 1) :
    acc+b.toNat%128*2^(7*index) < 2^64 := by
  by_cases hn : index=9
  · have hb := hg hn
    subst index
    simp only [Nat.reduceMul,Nat.reducePow] at ha ⊢
    omega
  · have hv := AsmCodec.unsigned_accumulate_bound acc index b ha
    have hp : 2^(7*(index+1)) ≤ 2^64 := Nat.pow_le_pow_right (by decide) (by omega)
    omega

theorem loop_value_bound (fuel index acc : Nat) (bytes : List UInt8) (d : Decoded)
    (hc : index+fuel=10) (ha : acc < 2^(7*index))
    (h : ProtobufVarint.decodeLoop fuel index acc bytes=.ok d) : d.value < 2^64 := by
  induction fuel generalizing index acc bytes with
  | zero => simp [ProtobufVarint.decodeLoop] at h
  | succ fuel ih =>
    cases bytes with
    | nil => simp [ProtobufVarint.decodeLoop] at h
    | cons b bs =>
      simp only [ProtobufVarint.decodeLoop] at h
      split at h
      · cases h
      · rename_i hg
        have guard : index=9 → b.toNat ≤ 1 := by
          simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,not_and] at hg
          intro he; have := hg he; omega
        split at h
        · cases h
          exact terminal_value_bound acc index b (by omega) ha guard
        · exact ih (index+1) _ bs (by omega) (AsmCodec.unsigned_accumulate_bound acc index b ha) h

theorem decode_value_bound (bytes : List UInt8) (d : Decoded)
    (h : ProtobufVarint.decode bytes=.ok d) : d.value < 2^64 :=
  loop_value_bound 10 0 0 bytes d rfl (by decide) h

end Libp2pAsm.Refinement.AsmProtobuf
