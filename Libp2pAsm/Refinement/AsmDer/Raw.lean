import Libp2pAsm.Refinement.AsmDer.Execution

namespace Libp2pAsm.Refinement.AsmDer
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

abbrev InputAt := AsmProtobuf.InputAt

def RawPost (ptr len : Word) (bytes : List UInt8) (t : State) : Prop :=
  DecodePost (if 2^64 < ptr.toNat+len.toNat then .error .range
    else if len=0 then .error .truncated else Spec.Codec.Der.decode bytes) t ∧ DecodeClear t

def rawReads (ptr len : Word) (bytes : List UInt8) : List (Nat × Word) :=
  if 2^64 < ptr.toNat+len.toNat then [] else if len=0 then [] else decodeReads ptr bytes

theorem initialise (s : State) (hra : s.getReg .x1=0)
    (hspan : (s.getReg .x10).toNat+(s.getReg .x11).toNat ≤ 2^64) :
    ∃ n t, n≤6 ∧ ReadTrace decoder 0 [] n (atPC s 65536) t ∧ t.pc=65628 ∧
      t.getReg .x10=s.getReg .x10 ∧ t.getReg .x11=s.getReg .x11 ∧
      t.getReg .x1=0 ∧ t.memory=s.memory := by
  by_cases hz : s.getReg .x11=0
  · refine ⟨1,?_,by decide,?trace,?post⟩
    case trace =>
      parser_read_step
      exact .nil _
    case post => simp [getReg_setReg,hra]
  · have hg := (Parser.range_iff (s.getReg .x10) (s.getReg .x11) hz).mpr hspan
    change s.getReg .x11+18446744073709551615 ≤ (18446744073709551615 : Word)-s.getReg .x10 at hg
    refine ⟨6,?_,by decide,?trace,?post⟩
    case trace =>
      repeat parser_read_step
      exact .nil _
    case post => simp [getReg_setReg,hra]

theorem range_error (s : State) (hra : s.getReg .x1=0)
    (hb : 2^64 < (s.getReg .x10).toNat+(s.getReg .x11).toNat) :
    ∃ t, ReadTrace decoder 0 [] 21 (atPC s 65536) t ∧ t.pc=0 ∧
      DecodePost (.error .range) t ∧ DecodeClear t := by
  have hn : s.getReg .x11≠0 := by
    intro hz; have := (s.getReg .x10).isLt; simp [hz] at hb; omega
  have hg : ¬s.getReg .x11+(-1 : Word) ≤ (-1 : Word)-s.getReg .x10 := by
    rw [Parser.range_iff _ _ hn]; omega
  change ¬s.getReg .x11+18446744073709551615 ≤ (18446744073709551615 : Word)-s.getReg .x10 at hg
  simp only [BitVec.ofNat_eq_ofNat] at *
  have hp : ∃ a, ReadTrace decoder 0 [] 5 (atPC s 65536) a ∧ a.pc=65556 ∧ a.getReg .x1=0 := by
    refine ⟨?_,?trace,?post⟩
    case trace =>
      repeat parser_read_step
      exact .nil _
    case post => simp [getReg_setReg,hra]
  obtain ⟨a,ha,hpc,hra'⟩ := hp
  obtain ⟨t,ht,hret,hout,_⟩ := error_return 0 a hra'
  exact ⟨t,by simpa using ha.append (readTrace_at_pc hpc ht),hret,
    error_post t .range hout,error_clear t 4 hout⟩

theorem raw_trace (s : State) (bytes : List UInt8) (hra : s.getReg .x1=0)
    (hm : s.memory.valid=true) (hi : InputAt s bytes) :
    ∃ n t, n≤129 ∧ ReadTrace decoder 0 (rawReads (s.getReg .x10) (s.getReg .x11) bytes)
      n (atPC s 65536) t ∧ t.pc=0 ∧ RawPost (s.getReg .x10) (s.getReg .x11) bytes t := by
  by_cases hb : 2^64 < (s.getReg .x10).toNat+(s.getReg .x11).toNat
  · obtain ⟨t,ht,hret,ho,hcl⟩ := range_error s hra hb
    exact ⟨21,t,by decide,by simpa only [rawReads,if_pos hb] using ht,hret,by simpa only [RawPost,if_pos hb] using And.intro ho hcl⟩
  obtain ⟨ni,a,hni,ha,hapc,hptr,hlen,hra',hmem⟩ := initialise s hra (by omega)
  by_cases hz : s.getReg .x11=0
  · obtain ⟨t,ht,hret,ho,hcl⟩ := empty_input a (hlen.trans hz) hra'
    exact ⟨ni+17,t,by omega,by simpa only [rawReads,if_neg hb,if_pos hz,List.nil_append] using ha.append (readTrace_at_pc hapc ht),hret,
      by simpa only [RawPost,if_neg hb,if_pos hz] using And.intro ho hcl⟩
  obtain ⟨hl,howned⟩ := hi (by omega) hz
  have hlw : a.getReg .x11=BitVec.ofNat 64 bytes.length := by rw [hlen,←hl]; simp
  obtain ⟨n,t,hn,ht,hret,ho,hcl⟩ := content_trace a bytes (by rw [←hl]; exact (s.getReg .x11).isLt)
    hlw hra' (by rw [hmem,hptr]; exact howned.reads hm)
  exact ⟨ni+n,t,by omega,by simpa only [rawReads,if_neg hb,if_neg hz,hptr,List.nil_append] using ha.append (readTrace_at_pc hapc ht),hret,
    by simpa only [RawPost,if_neg hb,if_neg hz] using And.intro ho hcl⟩

end Libp2pAsm.Refinement.AsmDer
