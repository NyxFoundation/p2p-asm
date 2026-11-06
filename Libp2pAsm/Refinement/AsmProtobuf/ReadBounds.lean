import Libp2pAsm.Refinement.AsmProtobuf.ReadExecution

namespace Libp2pAsm.Refinement.AsmProtobuf.Footprint
open Rv64 Rv64.Logic Rv64.Logic.Parser Spec.Codec

theorem count_bounds (fuel index : Nat) (bytes : List UInt8) :
    readCount fuel index bytes ≤ fuel ∧ readCount fuel index bytes ≤ bytes.length := by
  induction fuel generalizing index bytes with
  | zero => simp [readCount]
  | succ fuel ih =>
    cases bytes with
    | nil => simp [readCount]
    | cons b bs =>
      simp only [readCount,List.length_cons]
      split <;> (try omega)
      split <;> (try omega)
      have := ih (index+1) bs
      omega

theorem success_count (fuel index value : Nat) (bytes : List UInt8) (d : Decoded)
    (h : ProtobufVarint.decodeLoop fuel index value bytes = .ok d) :
    readCount fuel index bytes+index = d.consumed := by
  induction fuel generalizing index value bytes with
  | zero => simp [ProtobufVarint.decodeLoop] at h
  | succ fuel ih =>
    cases bytes with
    | nil => simp [ProtobufVarint.decodeLoop] at h
    | cons b bs =>
      simp only [ProtobufVarint.decodeLoop] at h
      split at h
      · cases h
      · rename_i hg
        split at h
        · rename_i hb; cases h; simp [readCount,hg,hb,Nat.add_comm]
        · rename_i hb
          have := ih (index+1) _ bs h
          simp only [readCount,if_neg hg,if_neg hb]
          omega

theorem byteReads_length (ptr : Word) (n : Nat) : (byteReads ptr n).length=n := by
  induction n generalizing ptr with
  | zero => rfl
  | succ n ih => simp [byteReads,ih]

theorem byteReads_member (ptr : Word) (n : Nat) (a : Nat × Word) :
    a ∈ byteReads ptr n → ∃ i, i<n ∧ a=(1,ptr+BitVec.ofNat 64 i) := by
  induction n generalizing ptr with
  | zero => simp [byteReads]
  | succ n ih =>
    intro h
    simp only [byteReads,List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0,by omega,by simp⟩
    · obtain ⟨i,hi,rfl⟩ := ih (ptr+1) h
      refine ⟨i+1,by omega,?_⟩
      congr 1
      rw [BitVec.ofNat_add,BitVec.add_assoc,BitVec.add_comm (1 : Word) (BitVec.ofNat 64 i)]
      rfl

/-- Every actual byte load is below the exclusive input end, even if that end is 2^64. -/
theorem byteReads_bounds (ptr : Word) (n length : Nat) (hn : n ≤ length)
    (hb : ptr.toNat+length ≤ 2^64) (a : Nat × Word) (ha : a ∈ byteReads ptr n) :
    a.1=1 ∧ ptr.toNat ≤ a.2.toNat ∧ a.2.toNat+1 ≤ ptr.toNat+length := by
  obtain ⟨i,hi,rfl⟩ := byteReads_member ptr n a ha
  have hs : ptr.toNat+i < 2^64 := by omega
  have hil : i < 2^64 := by omega
  simp [BitVec.toNat_add,Nat.mod_eq_of_lt hil,Nat.mod_eq_of_lt hs]
  omega

end Libp2pAsm.Refinement.AsmProtobuf.Footprint
