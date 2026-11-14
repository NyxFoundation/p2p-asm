import Libp2pAsm.Asm.Crypto.Util
import Libp2pAsm.Refinement.AsmCodec.Relocation
import Libp2pAsm.Rv64.Logic.ParserAccesses
import Libp2pAsm.Rv64.Logic.ParserExit
import Libp2pAsm.Rv64.Logic.Complete

namespace Libp2pAsm.Rv64.Logic.Parser.Wide
open Refinement.AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

/-- The frozen common error epilogue, used only as a proof slice of its caller. -/
def exitProgram (status : Fin 10) : Program :=
  ⟨65536,(Asm.Crypto.Util.finish status.val).flatten.toArray⟩

theorem exit_layout (status : Fin 10) : LeafLayout (exitProgram status) := by
  refine ⟨by decide +revert,by decide +revert,by decide +revert,?_,?_⟩
  · exact (by decide : ∀ status : Fin 10, ∀ j : Fin (exitProgram status).code.size,
      LeafInstr (exitProgram status).code[j]) status
  · exact (by decide : ∀ status : Fin 10, ∀ j : Fin (exitProgram status).code.size,
      AvoidsZero (codeAddress (exitProgram status) j) (exitProgram status).code[j]) status

theorem exit_no_stores (status : Fin 10) :
    ∀ i ∈ (exitProgram status).code, writesMemory i=false := by
  exact (by decide : ∀ status : Fin 10, ∀ i ∈ (exitProgram status).code, writesMemory i=false) status

theorem exit_trace (status : Fin 10) (s : State) (hra : s.getReg .x1=0) :
    ∃ t, AccessTrace (exitProgram status) 0 [] [] 16 (atPC s 65536) t ∧ t.pc=0 ∧ ErrorOutput status.val t := by
  have hs : (BitVec.ofNat 12 status.val).signExtend 64 = BitVec.ofNat 64 status.val :=
    (by decide : ∀ status : Fin 10,
      (BitVec.ofNat 12 status.val).signExtend 64 = BitVec.ofNat 64 status.val) status
  refine ⟨?_, ?trace, ?post⟩
  case trace =>
    repeat parser_access_step
    exact .nil _
  case post => simp [ErrorOutput,Asm.Crypto.Sha2.cleared,getReg_setReg] <;> decide +revert

/-- Instantiating this theorem requires equality with the actual containing code bytes. -/
theorem error_slice (whole : Program) (pc : Word) (start : Nat) (status : Fin 10) (s : State)
    (hslice : CodeSlice whole (relocated (exitProgram status) pc) start)
    (hplace : Placement (exitProgram status) pc 0)
    (halign : whole.base.toNat % 4=0) (hbound : whole.base.toNat+4*whole.code.size ≤ 2^64)
    (hra : s.getReg .x1=0) :
    ∃ t, AccessTrace whole 0 [] [] 16 (atPC s pc) t ∧ t.pc=0 ∧ ErrorOutput status.val t ∧
      WriteTrace whole 0 0 0 16 (atPC s pc) t := by
  obtain ⟨t,ht,hret,hout⟩ := exit_trace status s hra
  have hread := (ht.relocate (exit_layout status) hplace hra).embed hslice halign hbound
  have hwrite := ((ht.trace.noStores (exit_no_stores status) 0 0).relocate
    (exit_layout status) hplace hra).embed hslice halign hbound
  have hstart : relocateState (exitProgram status) pc 0 (atPC s 65536)=atPC s pc := by
    have h := relocate_proofEntry (exitProgram status) (atPC s pc) pc rfl rfl
    simp only [getReg_atPC,hra,proofEntry,setReg_atPC,atPC_atPC] at h
    have hz : s.setReg .x1 0=s := by
      have hz : s.setReg .x1 (s.getReg .x1)=s := by simp [LeanAsm.Rv64.State.setReg,LeanAsm.Rv64.State.getReg,LeanAsm.Rv64.Reg.toNat]
      simpa only [hra] using hz
    simpa only [hz] using h
  rw [hstart] at hread hwrite
  exact ⟨_,hread,by simp [relocateState,hret,relocatePC],errorOutput_remap hout,hwrite⟩

end Libp2pAsm.Rv64.Logic.Parser.Wide
