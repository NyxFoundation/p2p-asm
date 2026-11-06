import Libp2pAsm.Refinement.AsmDer.LongExecution

namespace Libp2pAsm.Refinement.AsmDer
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def decodeReads (ptr : Word) : List UInt8 → List (Nat × Word)
  | [] => []
  | tag::rest => [(1,ptr)] ++ if Spec.Codec.Der.supportedTag tag.toNat then
      match rest with
      | [] => []
      | first::tail => [(1,ptr+1)] ++ if first.toNat<128 then [] else longReads ptr first tail
    else []

theorem empty_input (s : State) (hlen : s.getReg .x11=0) (hra : s.getReg .x1=0) :
    ∃ t, ReadTrace decoder 0 [] 17 (atPC s 65628) t ∧ t.pc=0 ∧
      DecodePost (.error .truncated) t ∧ DecodeClear t := by
  have hp : ∃ a, ReadTrace decoder 0 [] 1 (atPC s 65628) a ∧ a.pc=65632 ∧ a.getReg .x1=0 := by
    refine ⟨?_,?trace,?post⟩
    case trace =>
      parser_read_step
      exact .nil _
    case post => simp [getReg_setReg,hra]
  obtain ⟨a,ha,hpc,hra'⟩ := hp
  obtain ⟨t,ht,hret,hout,_⟩ := error_return 1 a hra'
  exact ⟨t,by simpa using ha.append (readTrace_at_pc hpc ht),hret,
    error_post t .truncated hout,error_clear t 1 hout⟩

theorem unsupported_tag (s : State) (bytes : List UInt8) (tag : UInt8) (ptr : Word)
    (hi : TagInv s bytes tag ptr) (ht : Spec.Codec.Der.supportedTag tag.toNat≠true) :
    ∃ n t, n≤21 ∧ ReadTrace decoder 0 [] n (atPC s 65780) t ∧ t.pc=0 ∧
      DecodePost (.error .unsupportedTag) t ∧ DecodeClear t := by
  by_cases hh : tag.toNat%32=31
  · obtain ⟨t,htr,hret,ho⟩ := tag_high_error s bytes tag ptr hi hh
    exact ⟨19,t,by decide,htr,hret,error_post t .unsupportedTag ho,error_clear t 6 ho⟩
  · have hz : tag.toNat=0 ∨ tag.toNat=32 := by
      have hbad := mt (tag_supported tag).mpr ht
      omega
    obtain ⟨t,htr,hret,ho⟩ := tag_zero_error s bytes tag ptr hi hz
    exact ⟨21,t,by decide,htr,hret,error_post t .unsupportedTag ho,error_clear t 6 ho⟩

theorem after_second (s : State) (tag first : UInt8) (tail : List UInt8) (ptr : Word)
    (hl : tail.length<2^64) (ht : Spec.Codec.Der.supportedTag tag.toNat=true)
    (hi : HeaderInv s tail tag first ptr) :
    ∃ n t, n≤106 ∧ ReadTrace decoder 0 (if first.toNat<128 then [] else longReads ptr first tail)
      n (atPC s (if first.toNat<128 then 66536 else 66036)) t ∧ t.pc=0 ∧
      DecodePost (Spec.Codec.Der.decode (tag::first::tail)) t ∧ DecodeClear t := by
  by_cases hf : first.toNat<128
  · obtain ⟨n,t,hn,htr,hret,ho,hcl⟩ := content_result s tag 2 first.toNat tail.length
      (by have := first.toNat_lt; omega) hl hi.1 hi.2.2.1 hi.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2.1
    refine ⟨n,t,by omega,by simpa [hf] using htr,hret,?_,hcl⟩
    simpa [Spec.Codec.Der.decode,ht,hf,bind,Except.bind,pure,Except.pure,
      throw,throwThe,MonadExceptOf.throw] using ho
  · obtain ⟨n,t,hn,htr,hret,ho,hcl⟩ := long_run s tail tag first ptr hl (by omega) hi
    exact ⟨n,t,hn,by simpa [hf] using htr,hret,by rwa [long_spec tag first tail ht hf],hcl⟩

theorem content_trace (s : State) (bytes : List UInt8)
    (hl : bytes.length<2^64) (hlen : s.getReg .x11=BitVec.ofNat 64 bytes.length)
    (hra : s.getReg .x1=0) (hm : Reads s.memory (s.getReg .x10) bytes) :
    ∃ n t, n≤123 ∧ ReadTrace decoder 0 (decodeReads (s.getReg .x10) bytes) n
      (atPC s 65628) t ∧ t.pc=0 ∧ DecodePost (Spec.Codec.Der.decode bytes) t ∧ DecodeClear t := by
  cases bytes with
  | nil =>
    obtain ⟨t,ht,hret,ho,hcl⟩ := empty_input s (by simpa using hlen) hra
    exact ⟨17,t,by decide,ht,hret,ho,hcl⟩
  | cons tag rest =>
    obtain ⟨a,ha,hapc,hai⟩ := take_tag s tag rest hl hlen hra hm
    by_cases htag : Spec.Codec.Der.supportedTag tag.toNat=true
    · obtain ⟨b,hb,hbpc,hbi⟩ := tag_pass a (tag::rest) tag (s.getReg .x10) hai htag
      cases rest with
      | nil =>
        obtain ⟨t,ht,hret,ho⟩ := missing_second b tag (s.getReg .x10) hbi
        refine ⟨27,t,by decide,?_,hret,?_,error_clear t 1 ho⟩
        · simpa [decodeReads,htag] using (ha.append (readTrace_at_pc hapc hb)).append (readTrace_at_pc hbpc ht)
        · simpa [Spec.Codec.Der.decode,htag,bind,Except.bind,throw,throwThe,MonadExceptOf.throw]
            using error_post t .truncated ho
      | cons first tail =>
        obtain ⟨c,hc,hcpc,hci⟩ := second_byte b tag first tail (s.getReg .x10) hl hbi
        obtain ⟨n,t,hn,ht,hret,ho,hcl⟩ := after_second c tag first tail (s.getReg .x10)
          (by simp only [List.length_cons] at hl; omega) htag hci
        refine ⟨4+5+8+n,t,by omega,?_,hret,ho,hcl⟩
        have hp := ((ha.append (readTrace_at_pc hapc hb)).append (readTrace_at_pc hbpc hc)).append
          (readTrace_at_pc hcpc ht)
        simpa [decodeReads,htag,List.append_assoc] using hp
    · obtain ⟨n,t,hn,ht,hret,ho,hcl⟩ := unsupported_tag a (tag::rest) tag (s.getReg .x10) hai htag
      refine ⟨4+n,t,by omega,?_,hret,?_,hcl⟩
      · simpa [decodeReads,htag] using ha.append (readTrace_at_pc hapc ht)
      · simpa [Spec.Codec.Der.decode,htag,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] using ho

end Libp2pAsm.Refinement.AsmDer
