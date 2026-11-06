import Libp2pAsm.Refinement.AsmDer.EncodeContract

namespace Libp2pAsm.Tests.ParserProof.DerEncode
open Rv64 Rv64.Logic Rv64.Logic.Parser Refinement.AsmDer
open Refinement.AsmCodec (Returns Invocation)
open Refinement.AsmDer.Encode

set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def image : Program := ⟨524288,#[.ADDI .x8 .x0 17]++encoder.code++#[.SD .x10 .x11 0]⟩

def entry (tag value ptr cap : Word) (m : Memory) : State :=
  let s : State := { pc := 524292, regs := Vector.replicate 32 0xdeadbeef, memory := m }
  ((((s.setReg .x1 524288).setReg .x10 tag).setReg .x11 value).setReg .x12 ptr).setReg .x13 cap

theorem invocation (s : State) (hm : s.memory.valid=true)
    (hsep : ∀ r∈s.memory.regions,r.writable=true → r.endAddr≤524288 ∨ 524860≤r.base.toNat)
    (hra : s.getReg .x1=524288) : Invocation encoder image 524292 (s.getReg .x1) 1 s.memory := by
  rw [hra]
  refine ⟨⟨hm,by decide,by decide,by decide,?_⟩,
    ⟨by decide,by decide,by decide,by decide⟩,⟨by decide,by decide,?_⟩⟩
  · exact hsep
  · have h : ∀ j : Fin 141, image.code[1+j.val]'(by change 1+j.val<143; omega)=
        encoder.code[j.val]'j.isLt := by decide
    intro j hj; exact h ⟨j,hj⟩

def content (tag value cap : Word) : State := entry tag value 131073 cap
  (heap 131073 (Array.replicate 12 0xcc) true [])

theorem content_owned (tag value cap : Word) : InputAt (content tag value cap) (Array.replicate 12 0xcc) [] := by
  intro _
  refine ⟨rfl,?_,?_⟩
  case refine_2 => change 131073+12≤2^64; decide
  change headerSize value.toNat≤12
  have := headerSize_bounds value
  omega

/-- A concrete guarded, unaligned output mapping works for every 64-bit tag, length and capacity. -/
theorem content_returns (tag value cap : Word) : ∃ done,
    Returns image (relocated encoder 524292) 524288 157 (content tag value cap) done ∧
    Post (result tag value 131073 cap) done.state ∧
    MemoryPost (content tag value cap) done.state (Array.replicate 12 0xcc) [] (result tag value 131073 cap) ∧
    AccessTrace image 524288 [] (rawWrites tag value 131073 cap) done.steps (content tag value cap) done.state := by
  have hv := invocation (content tag value cap) (by change (heap 131073 (Array.replicate 12 0xcc) true []).valid=true; cbv)
    (by intro r hr _; change r∈(heap 131073 (Array.replicate 12 0xcc) true []).regions at hr
        simp [heap] at hr; subst r; left; decide) rfl
  obtain ⟨done,hr,ho,hm,ht,_⟩ := encode_embedded image 524292 1 (content tag value cap) _ [] hv rfl (content_owned tag value cap)
  exact ⟨done,hr,ho,hm,ht⟩

def metadata (tag value ptr cap : Word) : State := entry tag value ptr cap ⟨#[]⟩

theorem rejected_without_mapping (tag value ptr cap : Word) (e : Spec.Codec.Der.Error)
    (he : rawError tag value ptr cap=some e) : ∃ done,
    runUntil image 524288 157 (metadata tag value ptr cap)=.ok done ∧ ErrorOutput e.code done.state ∧
    AccessTrace image 524288 [] [] done.steps (metadata tag value ptr cap) done.state ∧
    done.state.memory=(metadata tag value ptr cap).memory := by
  have hv := invocation (metadata tag value ptr cap) (by cbv) (by simp [metadata,entry]) rfl
  have hi : InputAt (metadata tag value ptr cap) #[] [] := by
    intro h; change rawError tag value ptr cap=none at h; rw [he] at h; cases h
  obtain ⟨done,hr,ho,hm,ht,_⟩ := encode_embedded image 524292 1 (metadata tag value ptr cap) #[] [] hv rfl hi
  change Post (result tag value ptr cap) done.state at ho
  change AccessTrace image 524288 [] (rawWrites tag value ptr cap) _ _ _ at ht
  change MemoryPost (metadata tag value ptr cap) done.state #[] [] (result tag value ptr cap) at hm
  exact ⟨done,hr.run,by simpa [result,he,Post] using ho,by simpa [rawWrites,he] using ht,
    by simpa [result,he,MemoryPost] using hm⟩

theorem high_tag_priority : rawError 256 0 18446744073709551615 0=some .unsupportedTag := by rfl
theorem high_form_priority : rawError 31 0 18446744073709551615 0=some .unsupportedTag := by rfl
theorem zero_tag_priority : rawError 0 0 18446744073709551615 0=some .unsupportedTag := by rfl
theorem capacity_priority : rawError 4 0 18446744073709551615 1=some .capacity := by rfl
theorem range_rejection : rawError 4 0 18446744073709551615 2=some .range := by rfl

theorem max_length_result : result 4 18446744073709551615 131073 10=
    .ok [4,136,255,255,255,255,255,255,255,255] := by cbv

theorem max_length_returns : ∃ done,
    runUntil image 524288 157 (content 4 18446744073709551615 10)=.ok done ∧
    done.state.getReg .x11=10 ∧ done.state.memory=heap 131073
      (patchBytes (Array.replicate 12 0xcc) 0 [4,136,255,255,255,255,255,255,255,255]) true [] := by
  obtain ⟨done,hr,ho,hm,_⟩ := content_returns 4 18446744073709551615 10
  rw [max_length_result] at ho hm
  exact ⟨done,hr.run,ho.1,hm⟩

end Libp2pAsm.Tests.ParserProof.DerEncode
