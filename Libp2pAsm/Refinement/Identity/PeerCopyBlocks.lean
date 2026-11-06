import Libp2pAsm.Refinement.Identity.PeerPreflight
import Libp2pAsm.Rv64.Logic.ParserViews

namespace Libp2pAsm.Refinement.Identity.Peer
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def CopyInv (s : State) (base ptr : Word) (offset : Nat) (data : List UInt8) (written : Word)
    (bytes : Array UInt8) (frame : List Region) : Prop :=
  s.getReg .x5=base+BitVec.ofNat 64 offset ∧ s.getReg .x6=ptr ∧
    s.getReg .x7=BitVec.ofNat 64 data.length ∧ s.getReg .x29=written ∧ s.getReg .x1=0 ∧
    s.memory=heap base bytes true frame ∧ View (heap base bytes true frame) ptr data

theorem copy_read (s : State) (base ptr : Word) (offset : Nat) (b : UInt8) (data : List UInt8) (written : Word)
    (bytes : Array UInt8) (frame : List Region) (hl : (b::data).length<2^64)
    (hm : (heap base bytes true frame).valid=true) (hi : CopyInv s base ptr offset (b::data) written bytes frame) :
    ∃ t, AccessTrace program 0 [(1,ptr)] [] 2 (atPC s 66188) t ∧ t.pc=66196 ∧
      CopyInv t base ptr offset (b::data) written bytes frame ∧ t.getReg .x28=BitVec.ofNat 64 b.toNat := by
  rcases hi with ⟨hout,hptr,hcount,hw,hra,hmem,hview⟩
  have hn : s.getReg .x7≠0 := by rw [hcount]; exact word_length_nonzero _ hl (by simp)
  have hread := (hview.reads hm).head
  refine ⟨?_,?trace,?post⟩
  case trace =>
    repeat parser_access_step
    exact .nil _
  case post => simp_all [CopyInv,getReg_setReg]

theorem copy_advance (s : State) (base ptr : Word) (offset : Nat) (b : UInt8) (data : List UInt8) (written : Word)
    (bytes : Array UInt8) (frame : List Region) (hi : CopyInv s base ptr offset (b::data) written bytes frame) :
    ∃ t, AccessTrace program 0 [] [] 4 (atPC s 66200) t ∧ t.pc=66188 ∧
      CopyInv t base (ptr+1) (offset+1) data written bytes frame := by
  rcases hi with ⟨hout,hptr,hcount,hw,hra,hmem,hview⟩
  have hd := word_succ_decrement data.length
  refine ⟨?_,?trace,?post⟩
  case trace =>
    repeat parser_access_step
    exact .nil _
  case post =>
    simp_all [CopyInv,getReg_setReg,BitVec.ofNat_add,BitVec.add_assoc]
    exact hview.tail

theorem copy_byte (s : State) (base ptr : Word) (offset total : Nat) (b : UInt8) (data : List UInt8) (written : Word)
    (bytes : Array UInt8) (frame : List Region) (hl : (b::data).length<2^64)
    (hb : base.toNat+bytes.size≤2^64) (hi : offset<total) (htotal : total≤bytes.size)
    (hsep : DisjointSpans base total ptr (b::data).length)
    (hm : (heap base bytes true frame).valid=true) (hinv : CopyInv s base ptr offset (b::data) written bytes frame) :
    ∃ t, AccessTrace program 0 [(1,ptr)] [(1,base+BitVec.ofNat 64 offset)] 7 (atPC s 66188) t ∧
      t.pc=66188 ∧ CopyInv t base (ptr+1) (offset+1) data written (bytes.setIfInBounds offset b) frame := by
  obtain ⟨a,ha,hapc,hai,hab⟩ := copy_read s base ptr offset b data written bytes frame hl hm hinv
  obtain ⟨c,hc,hcpc,hcm,hcregs⟩ := store_byte program 66196 a .x5 .x28 0 base (BitVec.ofNat 64 b.toNat)
    offset bytes frame rfl (by decide) (by simpa using hai.1) hab hai.2.2.2.2.2.1 hm hb (by omega)
  have hbyte : (BitVec.ofNat 64 b.toNat).toNat.toUInt8=b := by have := b.toNat_lt; simp
  rw [hbyte] at hcm
  have hview := hai.2.2.2.2.2.2.heap_frame (ByteFrame.setIfInBounds b (by omega : 0≤offset) (by omega)) hsep
  have hci : CopyInv c base ptr offset (b::data) written (bytes.setIfInBounds offset b) frame := by
    refine ⟨(hcregs .x5).trans hai.1,(hcregs .x6).trans hai.2.1,(hcregs .x7).trans hai.2.2.1,
      (hcregs .x29).trans hai.2.2.2.1,(hcregs .x1).trans hai.2.2.2.2.1,hcm,hview⟩
  obtain ⟨t,ht,hpc,hti⟩ := copy_advance c base ptr offset b data written _ frame hci
  exact ⟨t,by simpa using ((ha.append (accessTrace_at_pc hapc hc)).append (accessTrace_at_pc hcpc ht)),hpc,hti⟩

end Libp2pAsm.Refinement.Identity.Peer
