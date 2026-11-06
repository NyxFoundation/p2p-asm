import Libp2pAsm.Refinement.AsmDer.EncodeWriteBlocks

namespace Libp2pAsm.Refinement.AsmDer.Encode
open Rv64 Rv64.Logic Rv64.Logic.Parser

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

theorem emit_short (s : State) (base value : Word) (bytes : Array UInt8) (frame : List Region)
    (hv : s.getReg .x11=value) (hb : s.getReg .x12=base) (hh : s.getReg .x31=2)
    (hra : s.getReg .x1=0) (hm : s.memory=heap base bytes true frame)
    (hvalid : (heap base bytes true frame).valid=true) (hspan : base.toNat+bytes.size≤2^64) (hsize : 2≤bytes.size) :
    ∃ t, AccessTrace encoder 0 [] [(1,base+1)] 18 (atPC s 65988) t ∧ t.pc=0 ∧
      t.getReg .x11=2 ∧ Clear t ∧ t.memory=heap base (bytes.setIfInBounds 1 value.toNat.toUInt8) true frame := by
  obtain ⟨a,ha,hpc,ham,hregs⟩ := store_byte encoder 65988 s .x12 .x11 1 base value 1 bytes frame rfl
    (by decide) (by rw [hb]; rfl) hv hm hvalid hspan (by omega)
  obtain ⟨t,ht,hret,hw,hcl,htm⟩ := finish a 2 ((hregs .x31).trans hh) ((hregs .x1).trans hra)
  exact ⟨t,by simpa using (ha.append (accessTrace_at_pc hpc (short_jump a))).append ht,
    hret,hw,hcl,htm.trans ham⟩

theorem emit_long (s : State) (base value : Word) (count : Nat) (bytes : Array UInt8) (frame : List Region)
    (hv : s.getReg .x11=value) (hb : s.getReg .x12=base) (hh : s.getReg .x31=BitVec.ofNat 64 (2+count))
    (hc : s.getReg .x29=BitVec.ofNat 64 count) (hra : s.getReg .x1=0)
    (hcount : 0<count ∧ count≤8) (hm : s.memory=heap base bytes true frame)
    (hvalid : (heap base bytes true frame).valid=true) (hspan : base.toNat+bytes.size≤2^64) (hsize : 2+count≤bytes.size) :
    ∃ t, AccessTrace encoder 0 [] ((1,base+1)::reverseWrites base 2 count) (21+6*count) (atPC s 65996) t ∧
      t.pc=0 ∧ t.getReg .x11=BitVec.ofNat 64 (2+count) ∧ Clear t ∧
      t.memory=heap base (patchBytes bytes 1 ((128+count).toUInt8::beBytes count value.toNat)) true frame := by
  obtain ⟨a,ha,hapc,hamark,hargs,ham⟩ := long_marker s count hcount.2 hc
  have har : ∀ r∈[Reg.x1,.x10,.x11,.x12,.x29,.x31],a.getReg r=s.getReg r := hargs
  obtain ⟨b,hbpath,hbpc,hbm,hbregs⟩ := store_byte encoder 66000 a .x12 .x5 1 base
    (BitVec.ofNat 64 (128+count)) 1 bytes frame rfl (by decide)
    (by rw [har .x12 (by simp),hb]; rfl) hamark (ham.trans hm) hvalid hspan (by omega)
  have hb1 := (hbregs .x1).trans ((har .x1 (by simp)).trans hra)
  have hb11 : b.getReg .x11=BitVec.ofNat 64 value.toNat := by rw [hbregs .x11,har .x11 (by simp),hv]; simp
  have hb12 := (hbregs .x12).trans ((har .x12 (by simp)).trans hb)
  have hb29 := (hbregs .x29).trans ((har .x29 (by simp)).trans hc)
  have hb31 := (hbregs .x31).trans ((har .x31 (by simp)).trans hh)
  have hsmall : 128+count<2^64 := by omega
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hsmall] at hbm
  obtain ⟨c,hcpath,hcpc,hci⟩ := long_cursor b base value.toNat count _ frame hb11 hb29 hb31 hb12 hb1 hbm
  have hm' : (heap base (bytes.setIfInBounds 1 (128+count).toUInt8) true frame).valid=true := by
    rw [←heap_valid_congr base bytes _ true frame (by simp)]; exact hvalid
  obtain ⟨d,hd,hdpc,hd31,hd1,hdm⟩ := emit_loop count c base 2 value.toNat (BitVec.ofNat 64 (2+count))
    _ frame hcount.2 value.isLt (by simpa using hsize) (by simpa using hspan) hm' hci
  obtain ⟨t,ht,hret,hw,hcl,htm⟩ := finish d _ hd31 hd1
  refine ⟨t,?_,hret,hw,hcl,?_⟩
  · have path := (((ha.append (accessTrace_at_pc hapc hbpath)).append (accessTrace_at_pc hbpc hcpath)).append
      (accessTrace_at_pc hcpc hd)).append (accessTrace_at_pc hdpc ht)
    have hn : 1+1+2+(6*count+1)+16=21+6*count := by omega
    simpa only [hn,List.nil_append,List.append_nil,List.cons_append,BitVec.ofNat_eq_ofNat] using path
  · rw [htm,hdm,reversePatch_eq]
    rfl

end Libp2pAsm.Refinement.AsmDer.Encode
