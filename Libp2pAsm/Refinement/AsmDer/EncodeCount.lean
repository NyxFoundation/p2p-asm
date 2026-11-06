import Libp2pAsm.Refinement.AsmDer.Specification
import Libp2pAsm.Refinement.AsmDer.Programs
import Libp2pAsm.Rv64.Logic.ParserAccessExit

namespace Libp2pAsm.Refinement.AsmDer
open Rv64 Rv64.Logic Rv64.Logic.Parser AsmCodec
open Spec.Codec.Der (significantBytes)

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def EncodeArgs (s t : State) : Prop :=
  ∀ r∈[Reg.x1,.x10,.x11,.x12,.x13],t.getReg r=s.getReg r

theorem EncodeArgs.trans {s t u : State} (h : EncodeArgs s t) (g : EncodeArgs t u) : EncodeArgs s u :=
  fun r hr => (g r hr).trans (h r hr)

theorem shift_byte_nat (n : Nat) (hn : n<2^64) :
    BitVec.ofNat 64 n >>> (8 : Nat)=BitVec.ofNat 64 (n/256) := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n/256<2^64 by omega)]

theorem count_step (s : State) (value count : Nat) (hv : 0<value) (hv64 : value<2^64)
    (hvalue : s.getReg .x28=BitVec.ofNat 64 value)
    (hcount : s.getReg .x29=BitVec.ofNat 64 count) :
    ∃ t, AccessTrace encoder 0 [] [] 4 (atPC s 65788) t ∧ t.pc=65788 ∧
      t.getReg .x28=BitVec.ofNat 64 (value/256) ∧ t.getReg .x29=BitVec.ofNat 64 (count+1) ∧ EncodeArgs s t := by
  have hn : s.getReg .x28≠0 := by rw [hvalue]; exact word_length_nonzero value hv64 (by omega)
  have hs := shift_byte_nat value hv64
  refine ⟨?_,?trace,?post⟩
  case trace =>
    repeat parser_access_step
    exact .nil _
  case post => simp [getReg_setReg,hs,BitVec.ofNat_add,EncodeArgs]

theorem count_loop (value : Nat) (s : State) (count : Nat) (hv : value<2^64)
    (hvalue : s.getReg .x28=BitVec.ofNat 64 value)
    (hcount : s.getReg .x29=BitVec.ofNat 64 count) :
    ∃ t, AccessTrace encoder 0 [] [] (4*(significantBytes value).length+1) (atPC s 65788) t ∧
      t.pc=65804 ∧ t.getReg .x29=BitVec.ofNat 64 (count+(significantBytes value).length) ∧ EncodeArgs s t := by
  induction value using Nat.strongRecOn generalizing s count with
  | ind value ih =>
    by_cases hz : value=0
    · subst value
      refine ⟨?_,?trace,?post⟩
      case trace =>
        simp only [significantBytes,↓reduceDIte,List.length_nil,Nat.mul_zero,Nat.zero_add]
        parser_access_step
        exact .nil _
      case post => simp [significantBytes,getReg_setReg,hcount,EncodeArgs]
    · obtain ⟨a,ha,hapc,hav,hac,hargs⟩ := count_step s value count (by omega) hv hvalue hcount
      have hdec : value/256<value := Nat.div_lt_self (by omega) (by decide)
      obtain ⟨t,ht,hpc,hc,htargs⟩ := ih (value/256) hdec a (count+1) (by omega) hav hac
      have hsize : (significantBytes value).length=(significantBytes (value/256)).length+1 := by
        rw [significantBytes,dif_neg hz]
        simp only [List.length_append,List.length_singleton]
      refine ⟨t,?_,hpc,?_,hargs.trans htargs⟩
      · simpa [hsize,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
          ha.append (accessTrace_at_pc hapc ht)
      · simpa [hsize,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc

end Libp2pAsm.Refinement.AsmDer
