import Libp2pAsm.Refinement.AsmDer.EncodeEmit

namespace Libp2pAsm.Refinement.AsmDer.Encode
open Rv64 Rv64.Logic Rv64.Logic.Parser
open Spec.Codec.Der (significantBytes)

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def headerBytes (tag value : Word) : List UInt8 :=
  if value.toNat<128 then [tag.toNat.toUInt8,value.toNat.toUInt8]
  else [tag.toNat.toUInt8,(128+(significantBytes value.toNat).length).toUInt8]++significantBytes value.toNat

def headerWrites (base value : Word) : List (Nat × Word) :=
  (1,base)::(1,base+1)::if value.toNat<128 then [] else reverseWrites base 2 (significantBytes value.toNat).length

theorem header_length (tag value : Word) : (headerBytes tag value).length=headerSize value.toNat := by
  unfold headerBytes headerSize; split <;> simp <;> omega

theorem header_spec (tag value : Word) (ht : Spec.Codec.Der.supportedTag tag.toNat=true) :
    Spec.Codec.Der.encodeHeader tag.toNat value.toNat=.ok (headerBytes tag value) := by
  have hv : ¬value.toNat≥2^64 := by have := value.isLt; omega
  simp [Spec.Codec.Der.encodeHeader,ht,hv,headerBytes,bind,Except.bind,pure,Except.pure]
  split <;> simp_all

theorem significant_positive (value : Nat) (hv : 0<value) : 0<(significantBytes value).length := by
  rw [significantBytes,dif_neg (show value≠0 by omega)]
  simp

theorem write_header (s : State) (tag value base : Word) (bytes : Array UInt8) (frame : List Region)
    (htag : s.getReg .x10=tag) (hv : s.getReg .x11=value) (hb : s.getReg .x12=base)
    (hh : s.getReg .x31=BitVec.ofNat 64 (headerSize value.toNat))
    (hc : ¬value.toNat<128 → s.getReg .x29=BitVec.ofNat 64 (significantBytes value.toNat).length)
    (hra : s.getReg .x1=0) (hm : s.memory=heap base bytes true frame)
    (hvalid : (heap base bytes true frame).valid=true) (hspan : base.toNat+bytes.size≤2^64)
    (hsize : headerSize value.toNat≤bytes.size) :
    ∃ n t, n≤72 ∧ AccessTrace encoder 0 [] (headerWrites base value) n (atPC s 65976) t ∧ t.pc=0 ∧
      t.getReg .x11=BitVec.ofNat 64 (headerSize value.toNat) ∧ Clear t ∧
      t.memory=heap base (patchBytes bytes 0 (headerBytes tag value)) true frame := by
  have hsizes := headerSize_bounds value
  obtain ⟨a,ha,hapc,ham,hregs⟩ := store_byte encoder 65976 s .x12 .x10 0 base tag 0 bytes frame rfl
    (by decide) (by simpa using hb) htag hm hvalid hspan (by omega)
  obtain ⟨b,hbpath,hbpc,hargs,hbm⟩ := choose_form a
  have hb11 := (hargs .x11 (by simp)).trans ((hregs .x11).trans hv)
  have hb12 := (hargs .x12 (by simp)).trans ((hregs .x12).trans hb)
  have hb31 := (hargs .x31 (by simp)).trans ((hregs .x31).trans hh)
  have hb1 := (hargs .x1 (by simp)).trans ((hregs .x1).trans hra)
  have hmem := hbm.trans ham
  have hvalid' : (heap base (bytes.setIfInBounds 0 tag.toNat.toUInt8) true frame).valid=true := by
    rw [←heap_valid_congr base bytes _ true frame (by simp)]; exact hvalid
  by_cases hshort : value.toNat<128
  · have ha31 : a.getReg .x31=(2 : Word) := by simpa [headerSize,hshort] using (hregs .x31).trans hh
    have hpc : b.pc=65988 := by simpa [ha31] using hbpc
    obtain ⟨t,ht,hret,hw,hcl,htm⟩ := emit_short b base value _ frame hb11 hb12
      (by simpa [headerSize,hshort] using hb31) hb1 hmem hvalid' (by simpa using hspan) (by simp; omega)
    exact ⟨21,t,by decide,by simpa [headerWrites,hshort] using
      ((ha.append (accessTrace_at_pc hapc hbpath)).append (accessTrace_at_pc hpc ht)),
      hret,by simpa [headerSize,hshort] using hw,hcl,by simpa [headerBytes,hshort,patchBytes] using htm⟩
  · have hcount := significant_length 8 value.toNat value.isLt
    have hpos := significant_positive value.toNat (by omega)
    have ha31 := (hregs .x31).trans hh
    have hne : a.getReg .x31≠(2 : Word) := by
      rw [ha31,headerSize,if_neg hshort]
      intro he
      have he' := congrArg BitVec.toNat he
      change (2+(significantBytes value.toNat).length)%2^64=2 at he'
      rw [Nat.mod_eq_of_lt (by omega)] at he'
      omega
    have hpc : b.pc=65996 := by simpa only [if_neg hne] using hbpc
    have hb29 := (hargs .x29 (by simp)).trans ((hregs .x29).trans (hc hshort))
    obtain ⟨t,ht,hret,hw,hcl,htm⟩ := emit_long b base value (significantBytes value.toNat).length _ frame
      hb11 hb12 (by simpa [headerSize,hshort] using hb31) hb29 hb1 ⟨hpos,hcount⟩
      hmem hvalid' (by simpa using hspan) (by simp; simpa [headerSize,hshort] using hsize)
    refine ⟨3+(21+6*(significantBytes value.toNat).length),t,by omega,?_,hret,?_,hcl,?_⟩
    · simpa [headerWrites,hshort] using
        (ha.append (accessTrace_at_pc hapc hbpath)).append (accessTrace_at_pc hpc ht)
    · simpa [headerSize,hshort] using hw
    · simpa [headerBytes,hshort,patchBytes,significant_eq_be] using htm

end Libp2pAsm.Refinement.AsmDer.Encode
