import Libp2pAsm.Refinement.AsmProtobuf.ReadBlocks
import Libp2pAsm.Refinement.AsmProtobuf.Contract

namespace Libp2pAsm.Refinement.AsmProtobuf.Footprint
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmCodec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def byteReads : Word → Nat → List (Nat × Word)
  | _,0 => []
  | ptr,n+1 => (1,ptr)::byteReads (ptr+1) n

theorem byteReads_one_add (ptr : Word) (n : Nat) :
    byteReads ptr (1+n) = (1,ptr)::byteReads (ptr+1) n := by
  rw [Nat.add_comm]; rfl

def readCount : Nat → Nat → List UInt8 → Nat
  | 0,_,_ => 0
  | _+1,_,[] => 0
  | fuel+1,index,b::rest =>
    if index == 9 && b.toNat > 1 then 1
    else if b.toNat < 128 then 1 else 1+readCount fuel (index+1) rest

/-- Exact load sequence for all terminal, overflow and truncated paths. -/
theorem scan (fuel : Nat) (s : State) (bytes : List UInt8) (acc count : Nat)
    (hf : 0 < fuel) (hc : count+fuel = 10) (ha : acc < 2^(7*count))
    (hl : bytes.length < 2^64) (hi : Inv s bytes acc count) :
    ∃ n t, n ≤ 17*fuel+17 ∧
      ReadTrace program 0 (byteReads (s.getReg .x10) (readCount fuel count bytes)) n (atPC s 65640) t ∧
      t.pc = 0 ∧ Post (Spec.Codec.ProtobufVarint.decodeLoop fuel count acc bytes) t := by
  induction fuel generalizing s bytes acc count with
  | zero => omega
  | succ fuel ih =>
    cases bytes with
    | nil =>
      obtain ⟨t, ht, hp, ho⟩ := empty s acc count hi
      exact ⟨17,t,by omega,ht,hp,ho⟩
    | cons b bs =>
      by_cases hg : count = 9 ∧ 1 < b.toNat
      · obtain ⟨rfl,hb⟩ := hg
        obtain ⟨t,ht,hp,ho⟩ := overflow s b bs acc hl hb hi
        exact ⟨22,t,by omega,by simpa [readCount,hb,byteReads] using ht,hp,
          by simpa [Spec.Codec.ProtobufVarint.decodeLoop,hb] using ho⟩
      have guard : count=9 → b.toNat ≤ 1 := by omega
      obtain ⟨nr,r,hnr,hr,hpc,hri,hptr⟩ := read s b bs acc count (by omega) ha hl guard hi
      by_cases hb : b.toNat < 128
      · obtain ⟨t,ht,hp,ho⟩ := terminal r b bs acc count hb hri
        exact ⟨nr+17,t,by omega,
          by simpa [readCount,Bool.and_eq_true,hg,hb,byteReads] using hr.append (readTrace_at_pc hpc ht),hp,
          by simpa [Spec.Codec.ProtobufVarint.decodeLoop,Bool.and_eq_true,hg,hb] using ho⟩
      · have hcount : count<9 := by have := guard; omega
        obtain ⟨u,hu,hupc,hui,huptr⟩ := continuation r b bs acc count hb hri
        obtain ⟨n,t,hn,ht,hp,ho⟩ := ih u bs (acc+b.toNat%128*2^(7*count)) (count+1)
          (by omega) (by omega) (unsigned_accumulate_bound acc count b ha) (by simp_all; omega) hui
        refine ⟨nr+5+n,t,by omega,?_,hp,?_⟩
        · have path := (hr.append (readTrace_at_pc hpc hu)).append (readTrace_at_pc hupc ht)
          simpa [readCount,show count ≠ 9 by omega,hb,byteReads_one_add,byteReads,huptr,hptr] using path
        · simpa [Spec.Codec.ProtobufVarint.decodeLoop,show count ≠ 9 by omega,hb] using ho

theorem initialise (s : State) (bytes : List UInt8)
    (hlen : s.getReg .x11 = BitVec.ofNat 64 bytes.length) (hra : s.getReg .x1 = 0)
    (hspan : (s.getReg .x10).toNat+(s.getReg .x11).toNat ≤ 2^64)
    (hr : Reads s.memory (s.getReg .x10) bytes) :
    ∃ n t, n ≤ 10 ∧ ReadTrace program 0 [] n (atPC s 65536) t ∧ t.pc = 65640 ∧
      Inv t bytes 0 0 ∧ t.getReg .x10 = s.getReg .x10 := by
  by_cases hz : s.getReg .x11 = 0
  · refine ⟨4, ?_, by decide, ?trace, ?post⟩
    case trace =>
      repeat parser_read_step
      exact .nil _
    case post => simp_all [Inv, getReg_setReg]
  · have hg := (Parser.range_iff (s.getReg .x10) (s.getReg .x11) hz).mpr hspan
    change s.getReg .x11+18446744073709551615 ≤ (18446744073709551615 : Word)-s.getReg .x10 at hg
    refine ⟨9, ?_, by decide, ?trace, ?post⟩
    case trace =>
      repeat parser_read_step
      exact .nil _
    case post => simp_all [Inv, getReg_setReg]

theorem range_return (s : State) (hra : s.getReg .x1 = 0) :
    ∃ t, ReadTrace program 0 [] 16 (atPC s 65556) t ∧ t.pc = 0 ∧ Output 4 0 0 t ∧ Cleared t := by
  refine ⟨?_, ?trace, ?post⟩
  case trace =>
    repeat parser_read_step
    exact .nil _
  case post => simp [Output, Cleared, Asm.Crypto.Sha2.cleared, getReg_setReg]

theorem range_error (s : State) (hra : s.getReg .x1 = 0)
    (hb : 2^64 < (s.getReg .x10).toNat+(s.getReg .x11).toNat) :
    ∃ t, ReadTrace program 0 [] 21 (atPC s 65536) t ∧ t.pc = 0 ∧ Output 4 0 0 t ∧ Cleared t := by
  have hn : s.getReg .x11 ≠ 0 := by
    intro hz; have := (s.getReg .x10).isLt; simp [hz] at hb; omega
  have hg : ¬s.getReg .x11+(-1 : Word) ≤ (-1 : Word)-s.getReg .x10 := by
    rw [Parser.range_iff _ _ hn]; omega
  change ¬s.getReg .x11+18446744073709551615 ≤ (18446744073709551615 : Word)-s.getReg .x10 at hg
  simp only [BitVec.ofNat_eq_ofNat] at *
  have hprefix : ∃ a, ReadTrace program 0 [] 5 (atPC s 65536) a ∧ a.pc = 65556 ∧ a.getReg .x1 = 0 := by
    refine ⟨?_, ?trace, ?post⟩
    case trace =>
      repeat parser_read_step
      exact .nil _
    case post => simp [getReg_setReg, hra]
  obtain ⟨a,ht,hp,hr⟩ := hprefix
  obtain ⟨t,hu,hpc,ho⟩ := range_return a hr
  exact ⟨t,by simpa using (ht.append (readTrace_at_pc hp hu)),hpc,ho⟩


/-- Metadata rejection and empty input have an empty actual load sequence. -/
def rawReads (ptr len : Word) (bytes : List UInt8) : List (Nat × Word) :=
  if 2^64 < ptr.toNat+len.toNat then []
  else if len=0 then [] else byteReads ptr (readCount 10 0 bytes)

theorem raw_trace (s : State) (bytes : List UInt8) (hra : s.getReg .x1=0)
    (hm : s.memory.valid=true) (hi : InputAt s bytes) :
    ∃ n t, n ≤ 256 ∧ ReadTrace program 0 (rawReads (s.getReg .x10) (s.getReg .x11) bytes)
      n (atPC s 65536) t ∧ t.pc=0 ∧ RawPost (s.getReg .x10) (s.getReg .x11) bytes t := by
  by_cases hb : 2^64 < (s.getReg .x10).toNat+(s.getReg .x11).toNat
  · obtain ⟨t,ht,hp,ho⟩ := range_error s hra hb
    exact ⟨21,t,by decide,by simpa only [rawReads,if_pos hb] using ht,hp,
      by simpa only [RawPost,if_pos hb] using ho⟩
  by_cases hz : s.getReg .x11=0
  · obtain ⟨n,a,hn,ht,hp,ha,hptr⟩ := initialise s [] (by simpa using hz) hra (by omega)
      (by intro i hi; simp at hi)
    obtain ⟨t,hu,hpc,ho⟩ := empty a 0 0 ha
    exact ⟨n+17,t,by omega,by simpa only [rawReads,if_neg hb,if_pos hz,List.nil_append]
      using (ht.append (readTrace_at_pc hp hu)),hpc,by simpa only [RawPost,if_neg hb,if_pos hz] using ho⟩
  obtain ⟨hl,hmapped⟩ := hi (by omega) hz
  have hlen : s.getReg .x11=BitVec.ofNat 64 bytes.length := by rw [←hl]; simp
  obtain ⟨ni,a,hni,ha,hapc,hai,hptr⟩ := initialise s bytes hlen hra (by omega) (hmapped.reads hm)
  obtain ⟨n,t,hn,ht,hp,ho⟩ := scan 10 a bytes 0 0 (by decide) rfl (by decide)
    (by rw [←hl]; exact (s.getReg .x11).isLt) hai
  exact ⟨ni+n,t,by omega,by simpa only [rawReads,if_neg hb,if_neg hz,hptr,List.nil_append]
    using (ha.append (readTrace_at_pc hapc ht)),hp,by simpa only [RawPost,if_neg hb,if_neg hz,Spec.Codec.ProtobufVarint.decode] using ho⟩

end Libp2pAsm.Refinement.AsmProtobuf.Footprint
