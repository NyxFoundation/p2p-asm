import Libp2pAsm.Refinement.AsmDer.Contract

namespace Libp2pAsm.Refinement.AsmDer
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmProtobuf.Footprint

/-- Byte offsets only; the long-form leading octet may be inspected twice. -/
theorem long_reads_member (ptr : Word) (first : UInt8) (tail : List UInt8)
    (hf : 128 ≤ first.toNat) (a : Nat × Word) (ha : a ∈ longReads ptr first tail) :
    ∃ i, 2 ≤ i ∧ i<10 ∧ i<2+tail.length ∧ a=(1,ptr+BitVec.ofNat 64 i) := by
  unfold longReads at ha
  cases he : longCheck first tail.length with
  | error e => simp [he] at ha
  | ok count =>
    have hc := long_check_ok first tail.length count hf he
    simp only [he,List.mem_append,List.mem_singleton] at ha
    rcases ha with rfl | ha
    · exact ⟨2,by decide,by decide,by omega,rfl⟩
    · split at ha
      · simp at ha
      · obtain ⟨i,hi,rfl⟩ := byteReads_member (ptr+2) count a ha
        refine ⟨2+i,by omega,by omega,by omega,?_⟩
        simp only [BitVec.ofNat_add,BitVec.add_assoc]; rfl

theorem decode_reads_member (ptr : Word) (bytes : List UInt8) (a : Nat × Word)
    (ha : a ∈ decodeReads ptr bytes) :
    ∃ i, i<10 ∧ i<bytes.length ∧ a=(1,ptr+BitVec.ofNat 64 i) := by
  cases bytes with
  | nil => simp [decodeReads] at ha
  | cons tag rest =>
    simp only [decodeReads,List.mem_append,List.mem_singleton] at ha
    rcases ha with rfl | ha
    · exact ⟨0,by decide,by simp,by simp⟩
    · split at ha
      · cases rest with
        | nil => simp at ha
        | cons first tail =>
          simp only [List.mem_append,List.mem_singleton] at ha
          rcases ha with rfl | ha
          · exact ⟨1,by decide,by simp,by simp⟩
          · split at ha
            · simp at ha
            · rename_i hf
              obtain ⟨i,_,hi,hl,he⟩ := long_reads_member ptr first tail (by omega) a ha
              exact ⟨i,hi,by simp only [List.length_cons]; omega,he⟩
      · simp at ha

/-- Every decoder read is in the first ten input bytes, including ranges ending at 2^64. -/
theorem decode_reads_bounds (ptr : Word) (bytes : List UInt8)
    (hs : ptr.toNat+bytes.length ≤ 2^64) (a : Nat × Word) (ha : a ∈ decodeReads ptr bytes) :
    a.1=1 ∧ ptr.toNat≤a.2.toNat ∧ a.2.toNat<ptr.toNat+bytes.length ∧ a.2.toNat<ptr.toNat+10 := by
  obtain ⟨i,hi,hl,rfl⟩ := decode_reads_member ptr bytes a ha
  have hsum : ptr.toNat+i<2^64 := by omega
  have hi64 : i<2^64 := by omega
  simp [BitVec.toNat_add,Nat.mod_eq_of_lt hi64,Nat.mod_eq_of_lt hsum]
  omega

/-- On success no payload byte is read, even when the content is much longer than the header. -/
theorem decode_reads_header (ptr : Word) (bytes : List UInt8) (d : Spec.Codec.Der.Decoded)
    (hd : Spec.Codec.Der.decode bytes=.ok d) (a : Nat × Word) (ha : a∈decodeReads ptr bytes) :
    ∃ i, i<d.header ∧ a=(1,ptr+BitVec.ofNat 64 i) := by
  cases bytes with
  | nil => simp [Spec.Codec.Der.decode] at hd
  | cons tag rest =>
    cases rest with
    | nil =>
      simp [Spec.Codec.Der.decode,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hd
      split at hd <;> cases hd
    | cons first tail =>
      have hdecode := hd
      simp only [Spec.Codec.Der.decode,bind,Except.bind,pure,Except.pure,
        throw,throwThe,MonadExceptOf.throw] at hd
      split at hd
      · cases hd
      · rename_i htag
        have htag' : Spec.Codec.Der.supportedTag tag.toNat=true := by simpa using htag
        split at hd
        · rename_i hf
          split at hd
          · cases hd
          · cases hd
            simp [decodeReads,htag',hf] at ha
            rcases ha with rfl | rfl
            · exact ⟨0,by change 0<2; decide,by simp⟩
            · exact ⟨1,by change 1<2; decide,by simp⟩
        · rename_i hf
          have hlong : longResult tag first tail=.ok d := by
            rwa [long_spec tag first tail htag' hf] at hdecode
          unfold longResult at hlong
          cases he : longCheck first tail.length with
          | error e => simp [he] at hlong
          | ok count =>
            simp only [he] at hlong
            repeat' (split at hlong <;> try cases hlong)
            all_goals
              have hc := long_check_ok first tail.length count (by omega) he
              simp only [decodeReads,htag',↓reduceIte,List.mem_append,List.mem_singleton,if_neg hf,
                longReads,he] at ha
              rcases ha with rfl | rfl | ha
              · exact ⟨0,by change 0<2+count; omega,by simp⟩
              · exact ⟨1,by change 1<2+count; omega,by simp⟩
              · rcases ha with rfl | ha
                · exact ⟨2,by change 2<2+count; omega,rfl⟩
                · split at ha
                  · simp at ha
                  · obtain ⟨i,hil,rfl⟩ := byteReads_member (ptr+2) count a ha
                    exact ⟨2+i,by change 2+i<2+count; omega,by simp only [BitVec.ofNat_add,BitVec.add_assoc]; rfl⟩

end Libp2pAsm.Refinement.AsmDer
