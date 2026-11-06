import Libp2pAsm.Asm.Crypto.Util
import Libp2pAsm.Refinement.AsmCodec.Relocation
import Libp2pAsm.Rv64.Logic.ParserReads
import Libp2pAsm.Rv64.Logic.Complete

namespace Libp2pAsm.Rv64.Logic.Parser
open Refinement.AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

/-- The frozen common error epilogue, used only as a proof slice of its caller. -/
def exitProgram (status : Fin 9) : Program :=
  ⟨65536,(Asm.Crypto.Util.finish status.val).flatten.toArray⟩

def ErrorOutput (status : Nat) (t : State) : Prop :=
  t.getReg .x10=BitVec.ofNat 64 status ∧
    ∀ r ∈ Asm.Crypto.Sha2.cleared, r ≠ .x10 → t.getReg r=0

theorem exit_layout (status : Fin 9) : LeafLayout (exitProgram status) := by
  refine ⟨by decide +revert,by decide +revert,by decide +revert,?_,?_⟩
  · exact (by decide : ∀ status : Fin 9, ∀ j : Fin (exitProgram status).code.size,
      LeafInstr (exitProgram status).code[j]) status
  · exact (by decide : ∀ status : Fin 9, ∀ j : Fin (exitProgram status).code.size,
      AvoidsZero (codeAddress (exitProgram status) j) (exitProgram status).code[j]) status

theorem exit_no_stores (status : Fin 9) :
    ∀ i ∈ (exitProgram status).code, writesMemory i=false := by
  exact (by decide : ∀ status : Fin 9, ∀ i ∈ (exitProgram status).code, writesMemory i=false) status

theorem exit_trace (status : Fin 9) (s : State) (hra : s.getReg .x1=0) :
    ∃ t, ReadTrace (exitProgram status) 0 [] 16 (atPC s 65536) t ∧ t.pc=0 ∧ ErrorOutput status.val t := by
  have hs : (BitVec.ofNat 12 status.val).signExtend 64 = BitVec.ofNat 64 status.val :=
    (by decide : ∀ status : Fin 9,
      (BitVec.ofNat 12 status.val).signExtend 64 = BitVec.ofNat 64 status.val) status
  refine ⟨?_, ?trace, ?post⟩
  case trace =>
    repeat parser_read_step
    exact .nil _
  case post => simp [ErrorOutput,Asm.Crypto.Sha2.cleared,getReg_setReg] <;> decide +revert

theorem errorOutput_remap {f : Word → Word} {ra : Word} {status : Nat} {t : State}
    (h : ErrorOutput status t) : ErrorOutput status (remap f ra t) := by
  refine ⟨by simpa using h.1,?_⟩
  intro r hr h10
  have hne : r ≠ .x1 := by intro he; subst r; simp [Asm.Crypto.Sha2.cleared] at hr
  simpa only [remap_get _ _ _ _ hne] using h.2 r hr h10

/-- Instantiating this theorem requires equality with the actual containing code bytes. -/
theorem error_slice (whole : Program) (pc : Word) (start : Nat) (status : Fin 9) (s : State)
    (hslice : CodeSlice whole (relocated (exitProgram status) pc) start)
    (hplace : Placement (exitProgram status) pc 0)
    (halign : whole.base.toNat % 4=0) (hbound : whole.base.toNat+4*whole.code.size ≤ 2^64)
    (hra : s.getReg .x1=0) :
    ∃ t, ReadTrace whole 0 [] 16 (atPC s pc) t ∧ t.pc=0 ∧ ErrorOutput status.val t ∧
      WriteTrace whole 0 0 0 16 (atPC s pc) t := by
  obtain ⟨t,ht,hret,hout⟩ := exit_trace status s hra
  have hread := (ht.relocate (exit_layout status) hplace hra).embed hslice halign hbound
  have hwrite := ((ht.trace.noStores (exit_no_stores status) 0 0).relocate
    (exit_layout status) hplace hra).embed hslice halign hbound
  have hstart : relocateState (exitProgram status) pc 0 (atPC s 65536)=atPC s pc := by
    have h := relocate_proofEntry (exitProgram status) (atPC s pc) pc rfl rfl
    simp only [getReg_atPC,hra,proofEntry,setReg_atPC,atPC_atPC] at h
    have hz : s.setReg .x1 0=s := by
      have hz : s.setReg .x1 (s.getReg .x1)=s := by simp [State.setReg,State.getReg,Reg.toNat]
      simpa only [hra] using hz
    simpa only [hz] using h
  rw [hstart] at hread hwrite
  exact ⟨_,hread,by simp [relocateState,hret,relocatePC],errorOutput_remap hout,hwrite⟩

end Libp2pAsm.Rv64.Logic.Parser
