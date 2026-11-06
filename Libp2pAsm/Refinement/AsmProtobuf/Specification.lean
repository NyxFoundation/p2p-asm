import Libp2pAsm.Spec.Codec.ProtobufVarint

namespace Libp2pAsm.Refinement.AsmProtobuf
open Spec.Codec

/-- Every successful scan consumes a nonempty prefix, including nonminimal forms. -/
theorem consumed_bounds (fuel index value : Nat) (bytes : List UInt8) (d : Decoded)
    (h : ProtobufVarint.decodeLoop fuel index value bytes = .ok d) :
    index < d.consumed ∧ d.consumed ≤ index + bytes.length ∧
      d.consumed ≤ index + fuel := by
  induction fuel generalizing index value bytes with
  | zero => simp [ProtobufVarint.decodeLoop] at h
  | succ fuel ih =>
    cases bytes with
    | nil => simp [ProtobufVarint.decodeLoop] at h
    | cons b bs =>
      simp only [ProtobufVarint.decodeLoop] at h
      split at h
      · cases h
      · split at h
        · cases h; simp
        · have := ih _ _ _ h; simp only [List.length_cons]; omega

theorem decode_consumed (bytes : List UInt8) (d : Decoded)
    (h : ProtobufVarint.decode bytes = .ok d) :
    0 < d.consumed ∧ d.consumed ≤ bytes.length ∧ d.consumed ≤ 10 := by
  simpa using consumed_bounds 10 0 0 bytes d h

/-- A caller cannot turn a uint64 enum into a supported kind by truncating it. -/
theorem high_enum_ne (n : Nat) (h : 2^32 ≤ n) : n ≠ 1 ∧ n ≠ 2 := by omega

theorem accepts_nonminimal_zero : ProtobufVarint.decode [128, 0] = .ok ⟨0, 2⟩ := by rfl

theorem accepts_ten_byte_zero :
    ProtobufVarint.decode [128,128,128,128,128,128,128,128,128,0] = .ok ⟨0,10⟩ := by rfl

theorem accepts_uint64_max :
    ProtobufVarint.decode [255,255,255,255,255,255,255,255,255,1] = .ok ⟨2^64-1,10⟩ := by rfl

end Libp2pAsm.Refinement.AsmProtobuf
