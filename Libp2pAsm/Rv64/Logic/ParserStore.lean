import Libp2pAsm.Rv64.Logic.ParserAccesses
import Libp2pAsm.Rv64.Logic.Writes

namespace Libp2pAsm.Rv64.Logic.Parser

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384

theorem store_byte (p : Program) (pc : Word) (s : State) (a b : Reg) (off : BitVec 12)
    (base value : Word) (index : Nat) (bytes : Array UInt8) (frame : List Region)
    (hf : p.fetch pc=.ok (.SB a b off)) (hpc : pc≠0)
    (hp : s.getReg a+off.signExtend 64=base+BitVec.ofNat 64 index)
    (hv : s.getReg b=value) (hm : s.memory=heap base bytes true frame)
    (hvalid : (heap base bytes true frame).valid=true)
    (hspan : base.toNat+bytes.size≤2^64) (hindex : index<bytes.size) :
    ∃ t, AccessTrace p 0 [] [(1,base+BitVec.ofNat 64 index)] 1 (atPC s pc) t ∧
      t.pc=pc+4 ∧ t.memory=heap base (bytes.setIfInBounds index value.toNat.toUInt8) true frame ∧
      ∀ r,t.getReg r=s.getReg r := by
  have hs := heap_store_at base value bytes frame index hvalid hspan hindex
  refine ⟨atPC (withMemory s (heap base (bytes.setIfInBounds index value.toNat.toUInt8) true frame)) (pc+4),?_,rfl,rfl,?_⟩
  · apply AccessTrace.cons (i := .SB a b off)
    · exact hpc
    · exact hf
    · simp [execInstr,storeReg_eq_atPC,hp,hv,hm,hs,bind,Except.bind,pure,Except.pure] <;> rfl
    · rfl
    · simp [stores,hp] <;> rfl
    · exact .nil _
  · intro r; simp

end Libp2pAsm.Rv64.Logic.Parser
