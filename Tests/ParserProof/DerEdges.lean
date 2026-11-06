import Tests.ParserProof.Der

namespace Libp2pAsm.Tests.ParserProof.Der
open Rv64 Rv64.Logic Rv64.Logic.Parser Refinement.AsmDer
open Refinement.AsmCodec (Returns Invocation)

set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def wrapping : State := entry 18446744073709551615 2 ⟨#[]⟩
def emptyInput : State := entry 18446744073709551615 0 ⟨#[]⟩

theorem wrapping_owned : InputAt wrapping [] := by
  intro h; have : ¬(wrapping.getReg .x10).toNat+(wrapping.getReg .x11).toNat≤2^64 := by decide
  exact False.elim (this h)

theorem empty_owned : InputAt emptyInput [] := by
  intro _ h; exact False.elim (h rfl)

theorem wrapping_returns : ∃ done, runUntil image 524288 129 wrapping=.ok done ∧
    DecodePost (.error .range) done.state ∧ ReadTrace image 524288 [] done.steps wrapping done.state ∧
    WriteTrace image 524288 0 0 done.steps wrapping done.state := by
  have hv := invocation wrapping (by cbv) (by simp [wrapping,entry]) rfl
  obtain ⟨done,hr,hout,_,hread,hwrite,_⟩ := decode_with_footprint image 524292 1 wrapping []
    hv rfl wrapping_owned (by intro h; exact False.elim (by revert h; decide))
  exact ⟨done,hr.run,(by simpa [RawPost,wrapping,entry,getReg_setReg] using hout.1),
    by simpa [rawReads,wrapping,entry,getReg_setReg] using hread,hwrite⟩

theorem empty_returns : ∃ done, runUntil image 524288 129 emptyInput=.ok done ∧
    DecodePost (.error .truncated) done.state ∧ ReadTrace image 524288 [] done.steps emptyInput done.state ∧
    WriteTrace image 524288 0 0 done.steps emptyInput done.state := by
  have hv := invocation emptyInput (by cbv) (by simp [emptyInput,entry]) rfl
  obtain ⟨done,hr,hout,_,hread,hwrite,_⟩ := decode_with_footprint image 524292 1 emptyInput []
    hv rfl empty_owned (by intro _ h; exact False.elim (h rfl))
  exact ⟨done,hr.run,hout.1,hread,hwrite⟩

def topInput : State := entry 18446744073709551614 2
  (heap 18446744073709551614 #[4,0] false [])

theorem top_owned : InputAt topInput [4,0] := by
  intro _ _
  refine ⟨rfl,0,by decide,by decide,by decide,by decide,?_⟩
  intro i hi
  have he : i=0 ∨ i=1 := by simp only [List.length_cons,List.length_nil] at hi; omega
  rcases he with rfl | rfl <;> rfl

theorem top_returns : ∃ done, runUntil image 524288 129 topInput=.ok done ∧
    DecodePost (.ok ⟨4,2,0,2⟩) done.state ∧
    ReadTrace image 524288 [(1,18446744073709551614),(1,18446744073709551615)]
      done.steps topInput done.state ∧ WriteTrace image 524288 0 0 done.steps topInput done.state := by
  have hv := invocation topInput (by cbv) (by intro r hr; simp [topInput,entry,heap] at hr; subst r; rfl) rfl
  obtain ⟨done,hr,hout,_,hread,hwrite,_⟩ := decode_with_footprint image 524292 1 topInput [4,0]
    hv rfl top_owned (by intro _ _; right; decide)
  exact ⟨done,hr.run,hout.1,hread,hwrite⟩

theorem max_length_spec : Spec.Codec.Der.decode [4,136,255,255,255,255,255,255,255,255]=.error .truncated := by rfl

end Libp2pAsm.Tests.ParserProof.Der
