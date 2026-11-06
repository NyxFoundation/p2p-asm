import Libp2pAsm.Refinement.AsmDer.LongBlocks

namespace Libp2pAsm.Refinement.AsmDer
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmCodec
open Spec.Codec.Der (Error Decoded)
open AsmProtobuf.Footprint (byteReads)

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def longResult (tag first : UInt8) (tail : List UInt8) : Except Error Decoded :=
  match longCheck first tail.length with
  | .error e => .error e
  | .ok count =>
    if tail.head? == some 0 then .error .nonMinimal
    else let length := (tail.take count).foldl (fun a b => 256*a+b.toNat) 0
      if length < 128 then .error .nonMinimal
      else if tail.length-count < length then .error .truncated
      else .ok ⟨tag,2+count,length,2+count+length⟩

def longReads (ptr : Word) (first : UInt8) (tail : List UInt8) : List (Nat × Word) :=
  match longCheck first tail.length with
  | .error _ => []
  | .ok count => [(1,ptr+2)] ++
      if tail.head? == some 0 then [] else byteReads (ptr+2) count

theorem long_check_ok (first : UInt8) (available count : Nat)
    (hf : 128 ≤ first.toNat) (h : longCheck first available=.ok count) :
    0<count ∧ count≤8 ∧ count≤available ∧ count=first.toNat%128 := by
  have hbyte := first.toNat_lt
  unfold longCheck at h
  repeat' (split at h <;> try cases h)
  all_goals simp_all; omega

theorem long_success (s : State) (tail : List UInt8) (tag first : UInt8) (ptr : Word) (count : Nat)
    (hl : tail.length < 2^64) (hc : 0<count ∧ count≤8 ∧ count≤tail.length)
    (hi : HeaderInv s tail tag first ptr) (hn : s.getReg .x17=BitVec.ofNat 64 count)
    (he : longCheck first tail.length=.ok count) :
    ∃ n t, n≤82 ∧ ReadTrace decoder 0 (longReads ptr first tail) n (atPC s 66340) t ∧
      t.pc=0 ∧ DecodePost (longResult tag first tail) t ∧ DecodeClear t := by
  cases tail with
  | nil => simp only [List.length_nil] at hc; omega
  | cons b bs =>
    simp only [List.length_cons] at he
    by_cases hb : b=0
    · subst b
      obtain ⟨t,ht,hpc,ho,hcl⟩ := leading_zero s bs tag first ptr hi
      exact ⟨18,t,by decide,by simpa [longReads,he] using ht,hpc,
        by simpa [longResult,he] using ho,hcl⟩
    · obtain ⟨a,ha,hapc,hai,hptr⟩ := leading_nonzero s b bs tag first ptr count hb hc.2.2 hi hn
      have htake : ((b::bs).take count).length=count := by rw [List.length_take,Nat.min_eq_left hc.2.2]
      obtain ⟨c,hcpath,hcpc,hc13,hc12,hc14,hc16,hc1⟩ := length_loop ((b::bs).take count) a 0
        (BitVec.ofNat 64 tag.toNat) (BitVec.ofNat 64 (2+count))
        (BitVec.ofNat 64 ((b::bs).length-count)) (by rw [htake]; omega) hai
      have hv := length_value_fits ((b::bs).take count) (by rw [htake]; exact hc.2.1)
      have hval : c.getReg .x13=BitVec.ofNat 64 (((b::bs).take count).foldl (fun a b => 256*a+b.toNat) 0) := by
        rw [hc13]; apply BitVec.eq_of_toNat_eq
        rw [length_value_exact _ (by rw [htake]; exact hc.2.1)]
        simp [Nat.mod_eq_of_lt hv]
      obtain ⟨n,t,hnt,ht,hret,ho,hcl⟩ := late_minimal c tag (2+count)
        (((b::bs).take count).foldl (fun a b => 256*a+b.toNat) 0)
        ((b::bs).length-count) hv (by omega) hc12 hc14 hval hc16 hc1
      refine ⟨5+(7*count+1)+n,t,by omega,?_,hret,?_,hcl⟩
      · have hp := (ha.append (readTrace_at_pc hapc hcpath)).append (readTrace_at_pc hcpc ht)
        simpa [longReads,he,hb,htake,hptr,List.append_assoc] using hp
      · simpa [longResult,he,hb] using ho

theorem long_run (s : State) (tail : List UInt8) (tag first : UInt8) (ptr : Word)
    (hl : tail.length < 2^64) (hf : 128 ≤ first.toNat) (hi : HeaderInv s tail tag first ptr) :
    ∃ n t, n≤106 ∧ ReadTrace decoder 0 (longReads ptr first tail) n (atPC s 66036) t ∧
      t.pc=0 ∧ DecodePost (longResult tag first tail) t ∧ DecodeClear t := by
  obtain ⟨n,a,hn,ha,ho⟩ := long_prefix s tail tag first ptr hl hi
  cases he : longCheck first tail.length with
  | error e =>
    simp only [LongOutcome,he] at ho
    exact ⟨n,a,by omega,by simpa [longReads,he] using ha,ho.1,
      by simpa [longResult,he] using ho.2.1,ho.2.2⟩
  | ok count =>
    simp only [LongOutcome,he] at ho
    have hb := long_check_ok first tail.length count hf he
    obtain ⟨m,t,hm,ht,hret,hpost,hclear⟩ := long_success a tail tag first ptr count hl
      ⟨hb.1,hb.2.1,hb.2.2.1⟩ ho.2.1 ho.2.2 he
    exact ⟨n+m,t,by omega,by simpa using ha.append (readTrace_at_pc ho.1 ht),hret,hpost,hclear⟩

theorem byte_beq_nat (b : UInt8) (n : Nat) (hn : n<256) :
    (b == n.toUInt8)=decide (b.toNat=n) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq]
  rw [←UInt8.toNat_inj]
  simp [UInt8.toNat_ofNat,Nat.mod_eq_of_lt hn]

theorem long_spec (tag first : UInt8) (tail : List UInt8)
    (htag : Spec.Codec.Der.supportedTag tag.toNat=true) (hf : ¬first.toNat<128) :
    Spec.Codec.Der.decode (tag::first::tail)=longResult tag first tail := by
  simp only [Spec.Codec.Der.decode,htag,Bool.not_true,ite_false,
    bind,Except.bind,pure,Except.pure,throw,throwThe,MonadExceptOf.throw,if_neg hf]
  have h128 := byte_beq_nat first 128 (by decide)
  have h255 := byte_beq_nat first 255 (by decide)
  change (first == (128 : UInt8))=decide (first.toNat=128) at h128
  change (first == (255 : UInt8))=decide (first.toNat=255) at h255
  rw [h128,h255]
  unfold longResult longCheck
  repeat' split <;> simp_all

end Libp2pAsm.Refinement.AsmDer
