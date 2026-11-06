import Libp2pAsm.Refinement.AsmDer.EncodeTag

namespace Libp2pAsm.Refinement.AsmDer.Encode
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmCodec
open Spec.Codec.Der (significantBytes)

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def headerSize (value : Nat) : Nat := if value<128 then 2 else 2+(significantBytes value).length

theorem headerSize_bounds (v : Word) : 2≤headerSize v.toNat ∧ headerSize v.toNat≤10 := by
  have hs := significant_length 8 v.toNat v.isLt
  unfold headerSize; split <;> omega

theorem select_length (s : State) :
    ∃ n t, n≤40 ∧ AccessTrace encoder 0 [] [] n (atPC s 65768) t ∧ t.pc=65812 ∧
      t.getReg .x31=BitVec.ofNat 64 (headerSize (s.getReg .x11).toNat) ∧
      t.getReg .x29=(if (s.getReg .x11).toNat<128 then s.getReg .x29
        else BitVec.ofNat 64 (significantBytes (s.getReg .x11).toNat).length) ∧ EncodeArgs s t := by
  by_cases hs : (s.getReg .x11).toNat<128
  · have hguard : s.getReg .x11<(128 : Word) := by simpa [BitVec.lt_def] using hs
    refine ⟨3,?_,by decide,?trace,?post⟩
    case trace =>
      repeat parser_access_step
      exact .nil _
    case post => simp [headerSize,hs,EncodeArgs,getReg_setReg]
  · have hguard : ¬s.getReg .x11<(128 : Word) := by simpa [BitVec.lt_def] using hs
    simp only [BitVec.ofNat_eq_ofNat] at *
    have hp : ∃ a, AccessTrace encoder 0 [] [] 5 (atPC s 65768) a ∧ a.pc=65788 ∧
        a.getReg .x28=s.getReg .x11 ∧ a.getReg .x29=0 ∧ EncodeArgs s a := by
      refine ⟨?_,?trace,?post⟩
      case trace =>
        repeat parser_access_step
        exact .nil _
      case post => simp [EncodeArgs,getReg_setReg]
    obtain ⟨a,ha,hapc,hav,hac,hargs⟩ := hp
    obtain ⟨b,hb,hbpc,hbcount,hbargs⟩ := count_loop (s.getReg .x11).toNat a 0
      (s.getReg .x11).isLt (by simpa using hav) hac
    have htail : ∃ t, AccessTrace encoder 0 [] [] 2 (atPC b 65804) t ∧ t.pc=65812 ∧
        t.getReg .x31=BitVec.ofNat 64 (2+(significantBytes (s.getReg .x11).toNat).length) ∧
        t.getReg .x29=BitVec.ofNat 64 (significantBytes (s.getReg .x11).toNat).length ∧ EncodeArgs b t := by
      refine ⟨?_,?trace,?post⟩
      case trace =>
        repeat parser_access_step
        exact .nil _
      case post => simp [getReg_setReg,hbcount,EncodeArgs,BitVec.ofNat_add,BitVec.add_comm]
    obtain ⟨t,ht,hpc,h31,h29,htargs⟩ := htail
    have hlen := significant_length 8 (s.getReg .x11).toNat (s.getReg .x11).isLt
    exact ⟨5+(4*(significantBytes (s.getReg .x11).toNat).length+1)+2,t,by omega,
      by simpa using (ha.append (accessTrace_at_pc hapc hb)).append (accessTrace_at_pc hbpc ht),
      hpc,by simpa [headerSize,hs] using h31,by simpa [hs] using h29,(hargs.trans hbargs).trans htargs⟩

def boundsError (ptr cap : Word) (count : Nat) : Option Spec.Codec.Der.Error :=
  if cap.toNat<count then some .capacity else if 2^64<ptr.toNat+count then some .range else none

theorem check_bounds (s : State) (count : Nat) (hc : 2≤count ∧ count≤10)
    (hn : s.getReg .x31=BitVec.ofNat 64 count) (hra : s.getReg .x1=0) :
    ∃ n t, n≤22 ∧ AccessTrace encoder 0 [] [] n (atPC s 65812) t ∧
      (match boundsError (s.getReg .x12) (s.getReg .x13) count with
      | some e => t.pc=0 ∧ ErrorOutput e.code t
      | none => t.pc=65976 ∧ EncodeArgs s t ∧ t.getReg .x31=s.getReg .x31 ∧ t.getReg .x29=s.getReg .x29) := by
  have hc64 : count<2^64 := by omega
  have hcn : s.getReg .x31≠0 := by rw [hn]; exact word_length_nonzero count hc64 (by omega)
  have hcnt : (s.getReg .x31).toNat=count := by rw [hn]; simp [Nat.mod_eq_of_lt hc64]
  have hcmp : s.getReg .x31≤s.getReg .x13 ↔ count≤(s.getReg .x13).toNat := by rw [BitVec.le_def,hcnt]
  by_cases hcap : (s.getReg .x13).toNat<count
  · have hg : ¬s.getReg .x31≤s.getReg .x13 := by rw [hcmp]; omega
    have hp : ∃ a, AccessTrace encoder 0 [] [] 1 (atPC s 65812) a ∧ a.pc=65816 ∧ a.getReg .x1=0 := by
      refine ⟨?_,?trace,?post⟩
      case trace =>
        parser_access_step
        exact .nil _
      case post => simp [hra]
    obtain ⟨a,ha,hpc,hr⟩ := hp
    obtain ⟨t,ht,hret,ho,_⟩ := error_return 3 a hr
    exact ⟨17,t,by decide,by simpa using ha.append (accessTrace_at_pc hpc ht),by simpa only [boundsError,if_pos hcap,Spec.Codec.Der.Error.code,BitVec.ofNat_eq_ofNat] using And.intro hret (show ErrorOutput 5 t from ho)⟩
  have hg := hcmp.mpr (show count≤(s.getReg .x13).toNat by omega)
  by_cases hspan : 2^64<(s.getReg .x12).toNat+count
  · have hrange : ¬s.getReg .x31+(-1 : Word)≤(-1 : Word)-s.getReg .x12 := by
      rw [range_iff _ _ hcn,hcnt]; omega
    change ¬s.getReg .x31+18446744073709551615≤(18446744073709551615 : Word)-s.getReg .x12 at hrange
    clear hn hcnt hcmp hc64
    simp only [BitVec.ofNat_eq_ofNat] at *
    have hp : ∃ a, AccessTrace encoder 0 [] [] 6 (atPC s 65812) a ∧ a.pc=65904 ∧ a.getReg .x1=0 := by
      refine ⟨?_,?trace,?post⟩
      case trace =>
        repeat parser_access_step
        exact .nil _
      case post => simp [getReg_setReg,hra]
    obtain ⟨a,ha,hpc,hr⟩ := hp
    obtain ⟨t,ht,hret,ho,_⟩ := error_return 4 a hr
    exact ⟨22,t,by decide,by simpa using ha.append (accessTrace_at_pc hpc ht),by simpa only [boundsError,if_neg hcap,if_pos hspan,Spec.Codec.Der.Error.code,BitVec.ofNat_eq_ofNat] using And.intro hret (show ErrorOutput 4 t from ho)⟩
  · have hrange : s.getReg .x31+(-1 : Word)≤(-1 : Word)-s.getReg .x12 := by
      rw [range_iff _ _ hcn,hcnt]; omega
    change s.getReg .x31+18446744073709551615≤(18446744073709551615 : Word)-s.getReg .x12 at hrange
    clear hn hcnt hcmp hc64
    simp only [BitVec.ofNat_eq_ofNat] at *
    refine ⟨7,?_,by decide,?trace,?post⟩
    case trace =>
      repeat parser_access_step
      exact .nil _
    case post => simp [boundsError,hcap,hspan,EncodeArgs,getReg_setReg]

end Libp2pAsm.Refinement.AsmDer.Encode
