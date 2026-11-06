import Libp2pAsm.Refinement.AsmProtobuf.ReadContract

namespace Libp2pAsm.Tests.ParserProof
open Rv64 Rv64.Logic Rv64.Logic.Parser Refinement.AsmCodec Refinement.AsmProtobuf

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def image : Program := ⟨524288,#[.ADDI .x8 .x0 17]++program.code++#[.SD .x10 .x11 0]⟩

def entry (ptr len : Word) (m : Memory) : State :=
  let s : State := { pc := 524292, regs := Vector.replicate 32 0xdeadbeef, memory := m }
  ((s.setReg .x1 524288).setReg .x10 ptr).setReg .x11 len

def content (bytes : List UInt8) : State :=
  entry 131073 (BitVec.ofNat 64 bytes.length) (heap 131073 (bytes++[0xcc]).toArray false [])

theorem invocation (s : State) (hm : s.memory.valid=true)
    (hro : ∀ r ∈ s.memory.regions, r.writable=false) (hra : s.getReg .x1=524288) :
    Invocation program image 524292 (s.getReg .x1) 1 s.memory := by
  rw [hra]
  refine ⟨⟨hm,by decide,by decide,by decide,?_⟩,
    ⟨by decide,by decide,by decide,by decide⟩,⟨by decide,by decide,?_⟩⟩
  · intro r hr hw; have := hro r hr; simp_all
  · have h : ∀ j : Fin 93, image.code[1+j.val]'(by change 1+j.val < 95; omega) =
        program.code[j.val]'j.isLt := by decide
    intro j hj; exact h ⟨j,hj⟩

theorem content_valid (bytes : List UInt8) (hb : bytes.length ≤ 10) :
    Invocation program image 524292 ((content bytes).getReg .x1) 1 (content bytes).memory := by
  apply invocation
  · change (heap 131073 (bytes++[0xcc]).toArray false []).valid=true
    simp [heap,Memory.valid,Region.valid,Region.endAddr]; omega
  · intro r hr; simp [content,entry,heap] at hr; subst r; rfl
  · rfl

theorem content_owned (bytes : List UInt8) (hb : bytes.length ≤ 10) : InputAt (content bytes) bytes := by
  intro _ _
  have hl : bytes.length < 2^64 := by omega
  refine ⟨by simp [content,entry,getReg_setReg,Nat.mod_eq_of_lt hl],0,?_,?_,?_,?_,?_⟩
  · simp [content,entry,heap]
  · simp [content,entry,heap,getReg_setReg]
  · simp [content,entry,heap,getReg_setReg]
  · simp [content,entry,getReg_setReg]; omega
  · intro i hi
    simp [content,entry,heap,getReg_setReg,List.getElem_append_left hi]

/-- This entire family is satisfiable with nonzero initial registers and unaligned input. -/
theorem content_returns (bytes : List UInt8) (hb : bytes.length ≤ 10) :
    ∃ done, Returns image (relocated program 524292) 524288 256 (content bytes) done ∧
      RawPost 131073 (BitVec.ofNat 64 bytes.length) bytes done.state ∧
      done.state.memory=(content bytes).memory ∧
      ReadTrace image 524288 (Footprint.rawReads 131073 (BitVec.ofNat 64 bytes.length) bytes)
        done.steps (content bytes) done.state ∧
      WriteTrace image 524288 0 0 done.steps (content bytes) done.state ∧
      done.state.getReg .x3=(content bytes).getReg .x3 ∧ done.state.getReg .x4=(content bytes).getReg .x4 := by
  apply decode_with_footprint image 524292 1 (content bytes) bytes (content_valid bytes hb) rfl
    (content_owned bytes hb)
  intro _ _; left
  change 131073+(BitVec.ofNat 64 bytes.length).toNat ≤ 524288
  simp; omega

theorem max_uint64_spec : Spec.Codec.ProtobufVarint.decode
    [255,255,255,255,255,255,255,255,255,1] = .ok ⟨2^64-1,10⟩ := by rfl

theorem overflow_spec : Spec.Codec.ProtobufVarint.decode
    [128,128,128,128,128,128,128,128,128,2] = .error .overflow := by rfl

theorem truncated_spec : Spec.Codec.ProtobufVarint.decode [128] = .error .truncated := by rfl

def wrapping : State := entry 18446744073709551615 2 ⟨#[]⟩
def emptyInput : State := entry 18446744073709551615 0 ⟨#[]⟩

theorem wrapping_invocation : Invocation program image 524292 (wrapping.getReg .x1) 1 wrapping.memory :=
  invocation wrapping (by cbv) (by simp [wrapping,entry]) rfl

theorem wrapping_owned : InputAt wrapping [] := by
  intro h; have : ¬(wrapping.getReg .x10).toNat+(wrapping.getReg .x11).toNat ≤ 2^64 := by decide
  exact False.elim (this h)

theorem empty_invocation : Invocation program image 524292 (emptyInput.getReg .x1) 1 emptyInput.memory :=
  invocation emptyInput (by cbv) (by simp [emptyInput,entry]) rfl

theorem empty_owned : InputAt emptyInput [] := by
  intro _ h; exact False.elim (h rfl)

theorem wrapping_returns : ∃ done, runUntil image 524288 256 wrapping=.ok done ∧
    Output 4 0 0 done.state ∧ ReadTrace image 524288 [] done.steps wrapping done.state := by
  obtain ⟨done,hr,hout,_,hread,_⟩ := decode_with_footprint image 524292 1 wrapping []
    wrapping_invocation rfl wrapping_owned (by intro h; exact False.elim (by revert h; decide))
  exact ⟨done,hr.run,(by simpa [RawPost,wrapping,entry,getReg_setReg] using hout.1),
    by simpa [Footprint.rawReads,wrapping,entry,getReg_setReg] using hread⟩

theorem empty_returns : ∃ done, runUntil image 524288 256 emptyInput=.ok done ∧
    DecodePost (.error .truncated) done.state ∧
      ReadTrace image 524288 [] done.steps emptyInput done.state := by
  obtain ⟨done,hr,hout,_,hread,_⟩ := decode_with_footprint image 524292 1 emptyInput []
    empty_invocation rfl empty_owned (by intro _ h; exact False.elim (h rfl))
  have hp : Post (.error .truncated) done.state := by
    simpa [RawPost,emptyInput,entry,getReg_setReg] using hout
  exact ⟨done,hr.run,hp.1,by simpa [Footprint.rawReads,emptyInput,entry,getReg_setReg] using hread⟩

def topInput : State := entry 18446744073709551614 2
  (heap 18446744073709551614 #[128,0] false [])

theorem top_owned : InputAt topInput [128,0] := by
  intro _ _
  refine ⟨rfl,0,by decide,by decide,by decide,by decide,?_⟩
  intro i hi
  have he : i=0 ∨ i=1 := by simp only [List.length_cons,List.length_nil] at hi; omega
  rcases he with rfl | rfl <;> rfl

/-- A real load from address 2^64-1 is allowed, and no subsequent wrapping load occurs. -/
theorem top_returns : ∃ done, runUntil image 524288 256 topInput=.ok done ∧
    DecodePost (.ok ⟨0,2⟩) done.state ∧
    ReadTrace image 524288 [(1,18446744073709551614),(1,18446744073709551615)]
      done.steps topInput done.state := by
  have hv := invocation topInput (by cbv) (by intro r hr; simp [topInput,entry,heap] at hr; subst r; rfl) rfl
  obtain ⟨done,hr,hout,_,hread,_⟩ := decode_with_footprint image 524292 1 topInput [128,0]
    hv rfl top_owned (by intro _ _; right; decide)
  have hp : Post (.ok ⟨0,2⟩) done.state := hout
  exact ⟨done,hr.run,hp.1,hread⟩

end Libp2pAsm.Tests.ParserProof
