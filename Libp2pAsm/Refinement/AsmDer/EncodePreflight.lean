import Libp2pAsm.Refinement.AsmDer.EncodeHeader

namespace Libp2pAsm.Refinement.AsmDer.Encode
open Rv64 Rv64.Logic Rv64.Logic.Parser

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def rawError (tag value ptr cap : Word) : Option Spec.Codec.Der.Error :=
  if Spec.Codec.Der.supportedTag tag.toNat then boundsError ptr cap (headerSize value.toNat)
  else some .unsupportedTag

def PreflightOutcome (s t : State) : Prop :=
  match rawError (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13) with
  | some e => t.pc=0 ∧ ErrorOutput e.code t
  | none => t.pc=65976 ∧ EncodeArgs s t ∧ t.getReg .x31=BitVec.ofNat 64 (headerSize (s.getReg .x11).toNat) ∧
      (¬(s.getReg .x11).toNat<128 → t.getReg .x29=BitVec.ofNat 64 (Spec.Codec.Der.significantBytes (s.getReg .x11).toNat).length)

theorem preflight (s : State) (hra : s.getReg .x1=0) :
    ∃ n t, n≤85 ∧ AccessTrace encoder 0 [] [] n (atPC s 65536) t ∧ PreflightOutcome s t := by
  obtain ⟨nt,a,hnt,ha,ho⟩ := tag_checks s hra
  by_cases htag : Spec.Codec.Der.supportedTag (s.getReg .x10).toNat=true
  · simp only [if_pos htag] at ho
    obtain ⟨nl,b,hnl,hb,hbpc,hb31,hb29,hbargs⟩ := select_length a
    have hab11 := ho.2 .x11 (by simp)
    have hargs : EncodeArgs s b := ho.2.trans hbargs
    have hb11 := hargs .x11 (by simp)
    have hb12 := hargs .x12 (by simp)
    have hb13 := hargs .x13 (by simp)
    rw [hab11] at hb31 hb29
    obtain ⟨nc,t,hnc,ht,hout⟩ := check_bounds b (headerSize (s.getReg .x11).toNat)
      (headerSize_bounds (s.getReg .x11)) hb31 ((hargs .x1 (by simp)).trans hra)
    rw [hb12,hb13] at hout
    refine ⟨nt+nl+nc,t,by omega,by simpa using ((ha.append (accessTrace_at_pc ho.1 hb)).append
      (accessTrace_at_pc hbpc ht)),?_⟩
    unfold PreflightOutcome rawError
    simp only [if_pos htag]
    cases he : boundsError (s.getReg .x12) (s.getReg .x13) (headerSize (s.getReg .x11).toNat) with
    | some e => simpa only [he] using hout
    | none =>
      simp only [he] at hout
      refine ⟨hout.1,hargs.trans hout.2.1,hout.2.2.1.trans hb31,?_⟩
      intro hlong
      rw [hout.2.2.2,hb29,if_neg hlong]
  · simp only [if_neg htag] at ho
    exact ⟨nt,a,by omega,ha,by simpa only [PreflightOutcome,rawError,if_neg htag,Spec.Codec.Der.Error.code] using ho⟩

def result (tag value ptr cap : Word) : Except Spec.Codec.Der.Error (List UInt8) :=
  match rawError tag value ptr cap with
  | some e => .error e
  | none => .ok (headerBytes tag value)

def InputAt (s : State) (bytes : Array UInt8) (frame : List Region) : Prop :=
  rawError (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13)=none →
    s.memory=heap (s.getReg .x12) bytes true frame ∧
      headerSize (s.getReg .x11).toNat≤bytes.size ∧ (s.getReg .x12).toNat+bytes.size≤2^64

def Post (res : Except Spec.Codec.Der.Error (List UInt8)) (s : State) : Prop :=
  match res with
  | .error e => ErrorOutput e.code s
  | .ok bytes => s.getReg .x11=BitVec.ofNat 64 bytes.length ∧ Clear s

def MemoryPost (s t : State) (bytes : Array UInt8) (frame : List Region)
    (res : Except Spec.Codec.Der.Error (List UInt8)) : Prop :=
  match res with
  | .error _ => t.memory=s.memory
  | .ok out => t.memory=heap (s.getReg .x12) (patchBytes bytes 0 out) true frame

def rawWrites (tag value ptr cap : Word) : List (Nat × Word) :=
  match rawError tag value ptr cap with
  | some _ => []
  | none => headerWrites ptr value

/-- Raw metadata rejection needs no mapped output and performs no access of either kind. -/
theorem raw_trace (s : State) (bytes : Array UInt8) (frame : List Region)
    (hra : s.getReg .x1=0) (hm : s.memory.valid=true) (hi : InputAt s bytes frame) :
    ∃ n t, n≤157 ∧ AccessTrace encoder 0 [] (rawWrites (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13))
      n (atPC s 65536) t ∧ t.pc=0 ∧ Post (result (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13)) t ∧
      MemoryPost s t bytes frame (result (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13)) := by
  obtain ⟨n,a,hn,ha,hout⟩ := preflight s hra
  have hmem : a.memory=s.memory := ha.memory_frame rfl
  cases he : rawError (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13) with
  | some e =>
    simp only [PreflightOutcome,he] at hout
    exact ⟨n,a,by omega,by simpa only [rawWrites,he] using ha,hout.1,
      by simpa only [Post,result,he] using hout.2,by simpa only [MemoryPost,result,he] using hmem⟩
  | none =>
    simp only [PreflightOutcome,he] at hout
    obtain ⟨howned,hsize,hspan⟩ := hi he
    obtain ⟨m,t,hmn,ht,hret,hw,hcl,htm⟩ := write_header a (s.getReg .x10) (s.getReg .x11) (s.getReg .x12)
      bytes frame (hout.2.1 .x10 (by simp)) (hout.2.1 .x11 (by simp)) (hout.2.1 .x12 (by simp))
      hout.2.2.1 hout.2.2.2 ((hout.2.1 .x1 (by simp)).trans hra) (hmem.trans howned)
      (by rwa [←howned]) hspan hsize
    exact ⟨n+m,t,by omega,by simpa only [rawWrites,he,List.nil_append] using ha.append (accessTrace_at_pc hout.1 ht),
      hret,by simpa only [result,he,Post,header_length] using And.intro hw hcl,
      by simpa only [result,he,MemoryPost] using htm⟩

end Libp2pAsm.Refinement.AsmDer.Encode
