import Libp2pAsm.Refinement.AsmDer.Footprint

namespace Libp2pAsm.Tests.ParserProof.Der
open Rv64 Rv64.Logic Rv64.Logic.Parser Refinement.AsmCodec Refinement.AsmDer

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def image : Program := ⟨524288,#[.ADDI .x8 .x0 17]++decoder.code++#[.SD .x10 .x11 0]⟩

def entry (ptr len : Word) (m : Memory) : State :=
  let s : State := { pc := 524292, regs := Vector.replicate 32 0xdeadbeef, memory := m }
  ((s.setReg .x1 524288).setReg .x10 ptr).setReg .x11 len

def content (bytes : List UInt8) : State :=
  entry 131073 (BitVec.ofNat 64 bytes.length) (heap 131073 (bytes++[0xcc]).toArray false [])

theorem invocation (s : State) (hm : s.memory.valid=true)
    (hro : ∀ r ∈ s.memory.regions, r.writable=false) (hra : s.getReg .x1=524288) :
    Invocation decoder image 524292 (s.getReg .x1) 1 s.memory := by
  rw [hra]
  refine ⟨⟨hm,by decide,by decide,by decide,?_⟩,
    ⟨by decide,by decide,by decide,by decide⟩,⟨by decide,by decide,?_⟩⟩
  · intro r hr hw; have := hro r hr; simp_all
  · have h : ∀ j : Fin 283, image.code[1+j.val]'(by change 1+j.val < 285; omega) =
        decoder.code[j.val]'j.isLt := by decide
    intro j hj; exact h ⟨j,hj⟩

theorem content_valid (bytes : List UInt8) (hb : bytes.length ≤ 260) :
    Invocation decoder image 524292 ((content bytes).getReg .x1) 1 (content bytes).memory := by
  apply invocation
  · change (heap 131073 (bytes++[0xcc]).toArray false []).valid=true
    simp [heap,Memory.valid,Region.valid,Region.endAddr]; omega
  · intro r hr; simp [content,entry,heap] at hr; subst r; rfl
  · rfl

theorem content_owned (bytes : List UInt8) (hb : bytes.length ≤ 260) : InputAt (content bytes) bytes := by
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
theorem content_returns (bytes : List UInt8) (hb : bytes.length ≤ 260) :
    ∃ done, Returns image (relocated decoder 524292) 524288 129 (content bytes) done ∧
      RawPost 131073 (BitVec.ofNat 64 bytes.length) bytes done.state ∧
      done.state.memory=(content bytes).memory ∧
      ReadTrace image 524288 (rawReads 131073 (BitVec.ofNat 64 bytes.length) bytes)
        done.steps (content bytes) done.state ∧
      WriteTrace image 524288 0 0 done.steps (content bytes) done.state ∧
      done.state.getReg .x3=(content bytes).getReg .x3 ∧ done.state.getReg .x4=(content bytes).getReg .x4 := by
  apply decode_with_footprint image 524292 1 (content bytes) bytes (content_valid bytes hb) rfl
    (content_owned bytes hb)
  intro _ _; left
  change 131073+(BitVec.ofNat 64 bytes.length).toNat ≤ 524288
  simp; omega

/-- Every content-error exit has a concrete valid mapping and arbitrary dirty registers. -/
def errorCases : List (List UInt8 × Spec.Codec.Der.Error) :=
  [([], .truncated), ([31], .unsupportedTag), ([4], .truncated),
   ([4,1], .truncated), ([4,128], .indefinite), ([4,255], .reserved),
   ([4,137], .overflow), ([4,130,1], .truncated), ([4,129,0], .nonMinimal),
   ([4,129,1], .nonMinimal), ([4,129,128], .truncated)]

theorem error_cases_spec : ∀ c∈errorCases, Spec.Codec.Der.decode c.1=.error c.2 := by
  simp [errorCases,Spec.Codec.Der.decode,Spec.Codec.Der.supportedTag,bind,Except.bind,
    pure,Except.pure,throw,throwThe,MonadExceptOf.throw]

theorem error_cases_return : ∀ c∈errorCases, ∃ done,
    runUntil image 524288 129 (content c.1)=.ok done ∧ DecodePost (.error c.2) done.state ∧
      done.state.memory=(content c.1).memory := by
  intro c hc
  have hl : c.1.length≤260 := by
    have h : ∀ c∈errorCases,c.1.length≤260 := by decide
    exact h c hc
  obtain ⟨done,hr,ho,hm,_⟩ := content_returns c.1 hl
  have hb : ¬2^64 < (131073 : Word).toNat+(BitVec.ofNat 64 c.1.length).toNat := by simp; omega
  refine ⟨done,hr.run,?_,hm⟩
  have he := error_cases_spec c hc
  have hs := ho.1
  simp only [RawPost] at ho
  by_cases hz : BitVec.ofNat 64 c.1.length=(0 : Word)
  · have hzero : c.1.length=0 := by
      have hh := congrArg BitVec.toNat hz
      simp at hh; omega
    have hempty : c.1=[] := List.length_eq_zero_iff.mp hzero
    have herr : c.2=.truncated := by simpa [hempty,Spec.Codec.Der.decode,throw,throwThe,MonadExceptOf.throw] using he.symm
    simpa only [if_neg hb,if_pos hz,herr] using hs
  · simpa only [if_neg hb,if_neg hz,he] using hs

def longInput : List UInt8 := [4,129,128]++List.replicate 128 0

theorem long_success_spec : Spec.Codec.Der.decode longInput=.ok ⟨4,3,128,131⟩ := by rfl

theorem long_success_return : ∃ done, runUntil image 524288 129 (content longInput)=.ok done ∧
    DecodePost (.ok ⟨4,3,128,131⟩) done.state ∧ done.state.memory=(content longInput).memory := by
  obtain ⟨done,hr,ho,hm,_⟩ := content_returns longInput (by decide)
  exact ⟨done,hr.run,ho.1,hm⟩

end Libp2pAsm.Tests.ParserProof.Der
