import Libp2pAsm.Refinement.Identity.PeerContract

namespace Libp2pAsm.Tests.ParserProof.PeerId
open Rv64 Rv64.Logic Rv64.Logic.Parser Refinement.Identity.Peer
open Refinement.AsmCodec (Returns Invocation)

set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def image : Program := ⟨524288,#[.ADDI .x8 .x0 17]++program.code++#[.SD .x10 .x11 0]⟩

def entry (kind key length out cap : Word) (m : Memory) : State :=
  let s : State := { pc := 524292, regs := Vector.replicate 32 0xdeadbeef, memory := m }
  (((((s.setReg .x1 524288).setReg .x10 kind).setReg .x11 key).setReg .x12 length).setReg .x13 out).setReg .x14 cap

theorem invocation (s : State) (hm : s.memory.valid=true)
    (hsep : ∀ r∈s.memory.regions,r.writable=true → r.endAddr≤524288 ∨ 525040≤r.base.toNat)
    (hra : s.getReg .x1=524288) : Invocation program image 524292 (s.getReg .x1) 1 s.memory := by
  rw [hra]
  refine ⟨⟨hm,by decide,by decide,by decide,?_⟩,
    ⟨by decide,by decide,by decide,by decide⟩,⟨by decide,by decide,?_⟩⟩
  · exact hsep
  · have h : ∀ j : Fin 186, image.code[1+j.val]'(by change 1+j.val<188; omega)=
        program.code[j.val]'j.isLt := by decide
    intro j hj; exact h ⟨j,hj⟩

def frame (data : List UInt8) : List Region := [⟨196611,data.toArray,false⟩]
def content (kind cap : Word) (data : List UInt8) : State :=
  entry kind 196611 (BitVec.ofNat 64 data.length) 131073 cap
    (heap 131073 (Array.replicate 42 0xcc) true (frame data))

theorem content_input (data : List UInt8) (hl : data.length≤33) :
    BytesAt (heap 131073 (Array.replicate 42 0xcc) true (frame data)) 196611 data := by
  refine ⟨1,by change 1<2; decide,by change 196611≤196611; decide,?_,?_,?_⟩
  · simp [heap,frame]
  · change 196611+data.length≤2^64; omega
  · intro i hi; simpa [heap,frame]

/-- Arbitrary key contents, dirty registers, unaligned byte buffers and an unwritten output guard. -/
theorem content_returns (kind cap : Word) (data : List UInt8)
    (hk : kind.toNat=1 ∨ kind.toNat=2) (hl : data.length=31+kind.toNat) : ∃ done,
    Returns image (relocated program 524292) 524288 384 (content kind cap data) done ∧
    Post (result kind 196611 (BitVec.ofNat 64 data.length) 131073 cap data) done.state ∧
    MemoryPost (content kind cap data) done.state (Array.replicate 42 0xcc) (frame data)
      (result kind 196611 (BitVec.ofNat 64 data.length) 131073 cap data) ∧
    AccessTrace image 524288 (rawReads kind 196611 (BitVec.ofNat 64 data.length) 131073 cap)
      (rawWrites kind 196611 (BitVec.ofNat 64 data.length) 131073 cap) done.steps (content kind cap data) done.state := by
  have hs : 32≤data.length ∧ data.length≤33 := by omega
  have hm : (content kind cap data).memory.valid=true := by
    change (heap 131073 (Array.replicate 42 0xcc) true (frame data)).valid=true
    simp [heap,frame,LeanAsm.Rv64.Memory.valid,Array.all_eq_true,LeanAsm.Rv64.Region.valid,LeanAsm.Rv64.Region.endAddr,LeanAsm.Rv64.Region.disjoint]
    omega
  have hv := invocation (content kind cap data) hm
    (by intro r hr hw; simp [content,entry,heap,frame] at hr
        rcases hr with rfl | rfl
        · left; decide
        · cases hw) rfl
  have hi : InputAt (content kind cap data) data (Array.replicate 42 0xcc) (frame data) := by
    intro _
    exact ⟨by change data.length%2^64=data.length; omega,rfl,content_input data hs.2,
      by change data.length+6≤42; omega,by change 131073+42≤2^64; decide⟩
  obtain ⟨done,hr,ho,hm,ht,_⟩ := peerId_embedded image 524292 1 (content kind cap data) data _ (frame data) hv rfl hi
  exact ⟨done,hr,ho,hm,ht⟩

def metadata (kind key length out cap : Word) : State := entry kind key length out cap ⟨#[]⟩

theorem rejected_without_mapping (kind key length out cap : Word) (e : Spec.Identity.PublicKey.Error)
    (he : rawError kind key length out cap=some e) : ∃ done,
    runUntil image 524288 384 (metadata kind key length out cap)=.ok done ∧ ErrorOutput e.code done.state ∧
    AccessTrace image 524288 [] [] done.steps (metadata kind key length out cap) done.state ∧
    done.state.memory=(metadata kind key length out cap).memory := by
  have hv := invocation (metadata kind key length out cap) (by cbv) (by simp [metadata,entry]) rfl
  have hi : InputAt (metadata kind key length out cap) [] #[] [] := by
    intro h; change rawError kind key length out cap=none at h; rw [he] at h; cases h
  obtain ⟨done,hr,ho,hm,ht,_⟩ := peerId_embedded image 524292 1 (metadata kind key length out cap) [] #[] [] hv rfl hi
  change Post (result kind key length out cap []) done.state at ho
  change AccessTrace image 524288 (rawReads kind key length out cap) (rawWrites kind key length out cap) _ _ _ at ht
  change MemoryPost (metadata kind key length out cap) done.state #[] [] (result kind key length out cap []) at hm
  exact ⟨done,hr.run,by simpa [result,he,Post] using ho,by simpa [rawReads,rawWrites,he] using ht,
    by simpa [result,he,MemoryPost] using hm⟩

end Libp2pAsm.Tests.ParserProof.PeerId
