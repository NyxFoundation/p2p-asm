import Libp2pAsm.Refinement.Identity.PeerPreflight
import Libp2pAsm.Refinement.Identity.PeerBody

namespace Libp2pAsm.Refinement.Identity.Peer
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmProtobuf.Footprint

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def result (kind key length out cap : Word) (data : List UInt8) : Except Spec.Identity.PublicKey.Error (List UInt8) :=
  match rawError kind key length out cap with
  | some e => .error e
  | none => .ok (canonical kind data)

def InputAt (s : State) (data : List UInt8) (bytes : Array UInt8) (frame : List Region) : Prop :=
  rawError (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13) (s.getReg .x14)=none →
    (s.getReg .x12).toNat=data.length ∧ s.memory=heap (s.getReg .x13) bytes true frame ∧
      BytesAt s.memory (s.getReg .x11) data ∧ data.length+6≤bytes.size ∧
      (s.getReg .x13).toNat+bytes.size≤2^64

def Post (res : Except Spec.Identity.PublicKey.Error (List UInt8)) (s : State) : Prop :=
  match res with
  | .error e => ErrorOutput e.code s
  | .ok bytes => s.getReg .x11=BitVec.ofNat 64 bytes.length ∧ Clear s

def MemoryPost (s t : State) (bytes : Array UInt8) (frame : List Region)
    (res : Except Spec.Identity.PublicKey.Error (List UInt8)) : Prop :=
  match res with
  | .error _ => t.memory=s.memory
  | .ok out => t.memory=heap (s.getReg .x13) (patchBytes bytes 0 out) true frame

def rawReads (kind key length out cap : Word) : List (Nat × Word) :=
  match rawError kind key length out cap with
  | some _ => []
  | none => byteReads key length.toNat

def rawWrites (kind key length out cap : Word) : List (Nat × Word) :=
  match rawError kind key length out cap with
  | some _ => []
  | none => byteReads out (length.toNat+6)

@[simp] theorem canonical_length (kind : Word) (data : List UInt8) : (canonical kind data).length=data.length+6 := by
  simp only [canonical,List.length_append,List.length_cons,List.length_nil]; omega

/-- All raw inputs terminate; ownership is required only after metadata validation. -/
theorem raw_trace (s : State) (data : List UInt8) (bytes : Array UInt8) (frame : List Region)
    (hra : s.getReg .x1=0) (hm : s.memory.valid=true) (hi : InputAt s data bytes frame) :
    ∃ n t, n≤384 ∧ AccessTrace program 0
      (rawReads (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13) (s.getReg .x14))
      (rawWrites (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13) (s.getReg .x14)) n (atPC s 65536) t ∧
      t.pc=0 ∧ Post (result (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13) (s.getReg .x14) data) t ∧
      MemoryPost s t bytes frame (result (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13) (s.getReg .x14) data) := by
  obtain ⟨n,a,hn,ha,hout⟩ := preflight s hra
  have hmem : a.memory=s.memory := ha.memory_frame rfl
  cases he : rawError (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13) (s.getReg .x14) with
  | some e =>
    simp only [he] at hout
    exact ⟨n,a,by omega,by simpa only [rawReads,rawWrites,he] using ha,hout.1,
      by simpa only [Post,result,he] using hout.2,by simpa only [MemoryPost,result,he] using hmem⟩
  | none =>
    simp only [he] at hout
    obtain ⟨hl,howned,hinput,hsize,hspan⟩ := hi he
    obtain ⟨hk,hkl,_,_,_,_,hsep⟩ := validated _ _ _ _ _ he
    have hsmall : data.length≤33 := by omega
    have hai : HeaderInv a (s.getReg .x10) (s.getReg .x11) (s.getReg .x12) (s.getReg .x13)
        (s.getReg .x12+6) bytes frame :=
      ⟨hout.2.1 .x10 (by simp),hout.2.1 .x11 (by simp),hout.2.1 .x12 (by simp),hout.2.1 .x13 (by simp),
        hout.2.2,(hout.2.1 .x1 (by simp)).trans hra,hmem.trans howned,by rwa [hmem]⟩
    have hdis : DisjointSpans (s.getReg .x13) (data.length+6) (s.getReg .x11) data.length := by
      unfold DisjointSpans at *; omega
    obtain ⟨t,ht,hret,hw,hcl,htm⟩ := body a _ _ _ _ data bytes frame hai hl hsmall (by rwa [←howned]) hdis hsize hspan
    refine ⟨n+(30+7*data.length),t,by omega,?_,hret,?_,?_⟩
    · simpa only [rawReads,rawWrites,he,hl,List.nil_append] using ha.append (accessTrace_at_pc hout.1 ht)
    · simpa only [result,he,Post,canonical_length] using And.intro hw hcl
    · simpa only [result,he,MemoryPost] using htm

end Libp2pAsm.Refinement.Identity.Peer
