import Libp2pAsm.Refinement.AsmDer.EncodeLoop
import Libp2pAsm.Refinement.AsmDer.EncodePrepare

namespace Libp2pAsm.Refinement.AsmDer.Encode
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def WriteArgs (s t : State) : Prop :=
  ∀ r∈[Reg.x1,.x10,.x11,.x12,.x29,.x31],t.getReg r=s.getReg r

theorem choose_form (s : State) :
    ∃ t, AccessTrace encoder 0 [] [] 2 (atPC s 65980) t ∧
      t.pc=(if s.getReg .x31=2 then 65988 else 65996) ∧ WriteArgs s t ∧ t.memory=s.memory := by
  by_cases hn : s.getReg .x31=2
  · refine ⟨?_,?trace,?post⟩
    case trace =>
      repeat parser_access_step
      exact .nil _
    case post => simp [hn,WriteArgs,getReg_setReg]
  · simp only [BitVec.ofNat_eq_ofNat] at *
    refine ⟨?_,?trace,?post⟩
    case trace =>
      repeat parser_access_step
      exact .nil _
    case post => simp [hn,WriteArgs,getReg_setReg]

theorem marker_word (count : Nat) (hc : count≤8) :
    BitVec.ofNat 64 count ||| (128 : Word)=BitVec.ofNat 64 (128+count) := by
  have h : ∀ n : Fin 9, BitVec.ofNat 64 n.val ||| (128 : Word)=BitVec.ofNat 64 (128+n.val) := by decide
  exact h ⟨count,by omega⟩

theorem long_marker (s : State) (count : Nat) (hc : count≤8)
    (hn : s.getReg .x29=BitVec.ofNat 64 count) :
    ∃ t, AccessTrace encoder 0 [] [] 1 (atPC s 65996) t ∧ t.pc=66000 ∧
      t.getReg .x5=BitVec.ofNat 64 (128+count) ∧ WriteArgs s t ∧ t.memory=s.memory := by
  have hmark := marker_word count hc
  refine ⟨?_,?trace,?post⟩
  case trace =>
    parser_access_step
    exact .nil _
  case post => simp [hmark,WriteArgs,getReg_setReg]

theorem long_cursor (s : State) (base : Word) (value count : Nat) (bytes : Array UInt8) (frame : List Region)
    (hv : s.getReg .x11=BitVec.ofNat 64 value) (hc : s.getReg .x29=BitVec.ofNat 64 count)
    (hh : s.getReg .x31=BitVec.ofNat 64 (2+count)) (hb : s.getReg .x12=base)
    (hra : s.getReg .x1=0) (hm : s.memory=heap base bytes true frame) :
    ∃ t, AccessTrace encoder 0 [] [] 2 (atPC s 66004) t ∧ t.pc=66012 ∧
      EmitInv t base 2 value count (BitVec.ofNat 64 (2+count)) bytes frame := by
  refine ⟨?_,?trace,?post⟩
  case trace =>
    repeat parser_access_step
    exact .nil _
  case post =>
    simp_all [EmitInv,getReg_setReg,BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.add_comm]

def Clear (s : State) : Prop := ∀ r∈Asm.Crypto.Sha2.cleared,r≠.x11 → s.getReg r=0

theorem finish (s : State) (written : Word) (hw : s.getReg .x31=written) (hra : s.getReg .x1=0) :
    ∃ t, AccessTrace encoder 0 [] [] 16 (atPC s 66036) t ∧ t.pc=0 ∧
      t.getReg .x11=written ∧ Clear t ∧ t.memory=s.memory := by
  refine ⟨?_,?trace,?post⟩
  case trace =>
    repeat parser_access_step
    exact .nil _
  case post => simp [getReg_setReg,Clear,Asm.Crypto.Sha2.cleared]

theorem short_jump (s : State) : AccessTrace encoder 0 [] [] 1 (atPC s 65992) (atPC s 66036) := by
  parser_access_step
  exact .nil _

end Libp2pAsm.Refinement.AsmDer.Encode
