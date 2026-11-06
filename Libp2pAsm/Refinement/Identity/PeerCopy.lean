import Libp2pAsm.Refinement.Identity.PeerCopyBlocks

namespace Libp2pAsm.Refinement.Identity.Peer
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmProtobuf.Footprint

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

theorem copy_loop (data : List UInt8) (s : State) (base ptr : Word) (offset total : Nat) (written : Word)
    (bytes : Array UInt8) (frame : List Region) (hl : data.length<2^64)
    (hb : base.toNat+bytes.size≤2^64) (hi : offset+data.length≤total) (htotal : total≤bytes.size)
    (hsep : DisjointSpans base total ptr data.length)
    (hm : (heap base bytes true frame).valid=true) (hinv : CopyInv s base ptr offset data written bytes frame) :
    ∃ t, AccessTrace program 0 (byteReads ptr data.length) (byteReads (base+BitVec.ofNat 64 offset) data.length)
      (7*data.length+1) (atPC s 66188) t ∧ t.pc=66216 ∧ t.getReg .x29=written ∧ t.getReg .x1=0 ∧
      t.memory=heap base (patchBytes bytes offset data) true frame := by
  induction data generalizing s ptr offset bytes with
  | nil =>
    rcases hinv with ⟨hout,hptr,hcount,hw,hra,hmem,hview⟩
    refine ⟨?_,?trace,?post⟩
    case trace =>
      parser_access_step
      exact .nil _
    case post => simp [getReg_setReg,hw,hra,hmem,patchBytes]
  | cons b data ih =>
    obtain ⟨a,ha,hapc,hai⟩ := copy_byte s base ptr offset total b data written bytes frame hl hb
      (by simp only [List.length_cons] at hi; omega) htotal hsep hm hinv
    have hv := hinv.2.2.2.2.2.2
    have hsep' := hsep.tail hv.nonwrap
    have hm' : (heap base (bytes.setIfInBounds offset b) true frame).valid=true := by
      rw [←heap_valid_congr base bytes _ true frame (by simp)]; exact hm
    obtain ⟨t,ht,hpc,hout⟩ := ih a (ptr+1) (offset+1) _ (by simp only [List.length_cons] at hl; omega)
      (by simpa using hb) (by simp only [List.length_cons] at hi; omega) (by simpa using htotal) hsep' hm' hai
    refine ⟨t,?_,hpc,hout⟩
    have he : base+BitVec.ofNat 64 (offset+1)=(base+BitVec.ofNat 64 offset)+1 := by rw [BitVec.ofNat_add,BitVec.add_assoc]; rfl
    simpa [byteReads,List.length_cons,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,he] using
      (ha.append (accessTrace_at_pc hapc ht))

end Libp2pAsm.Refinement.Identity.Peer
