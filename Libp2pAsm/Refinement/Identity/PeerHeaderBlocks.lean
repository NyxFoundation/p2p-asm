import Libp2pAsm.Refinement.Identity.PeerCopy

namespace Libp2pAsm.Refinement.Identity.Peer
open Rv64 Rv64.Logic Rv64.Logic.Parser

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def HeaderInv (s : State) (kind key length out written : Word) (bytes : Array UInt8) (frame : List Region) : Prop :=
  s.getReg .x10=kind ∧ s.getReg .x11=key ∧ s.getReg .x12=length ∧ s.getReg .x13=out ∧
    s.getReg .x29=written ∧ s.getReg .x1=0 ∧ s.memory=heap out bytes true frame ∧ s.memory.valid=true

def putPC (i : Fin 6) : Word := (#[66136,66144,66152,66156,66164,66168] : Array Word)[i]
def putReg (i : Fin 6) : Reg := (#[.x0,.x5,.x5,.x10,.x5,.x12] : Array Reg)[i]

theorem put_fetch (i : Fin 6) : program.fetch (putPC i)=.ok (.SB .x13 (putReg i) (BitVec.ofNat 12 i.val)) := by
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by have := i.isLt; omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem put (i : Fin 6) (s : State) (kind key length out written value : Word) (bytes : Array UInt8) (frame : List Region)
    (hi : HeaderInv s kind key length out written bytes frame) (hv : s.getReg (putReg i)=value)
    (hs : 6≤bytes.size) (hb : out.toNat+bytes.size≤2^64) :
    ∃ t, AccessTrace program 0 [] [(1,out+BitVec.ofNat 64 i.val)] 1 (atPC s (putPC i)) t ∧ t.pc=putPC i+4 ∧
      HeaderInv t kind key length out written (bytes.setIfInBounds i.val value.toNat.toUInt8) frame := by
  rcases hi with ⟨hk,hkey,hl,ho,hw,hra,hm,hvalid⟩
  have hoff : (BitVec.ofNat 12 i.val).signExtend 64=BitVec.ofNat 64 i.val :=
    (by decide : ∀ j : Fin 6, (BitVec.ofNat 12 j.val).signExtend 64=BitVec.ofNat 64 j.val) i
  obtain ⟨t,ht,hpc,htm,hregs⟩ := store_byte program (putPC i) s .x13 (putReg i) (BitVec.ofNat 12 i.val)
    out value i.val bytes frame (put_fetch i) ((by decide : ∀ j : Fin 6,putPC j≠0) i) (by rw [ho,hoff]) hv hm
    (by rwa [←hm]) hb (by have := i.isLt; omega)
  refine ⟨t,ht,hpc,(hregs .x10).trans hk,(hregs .x11).trans hkey,(hregs .x12).trans hl,
    (hregs .x13).trans ho,(hregs .x29).trans hw,(hregs .x1).trans hra,htm,?_⟩
  rw [htm,←heap_valid_congr out bytes _ true frame (by simp),←hm]
  exact hvalid

def markPC (i : Fin 3) : Word := (#[66140,66148,66160] : Array Word)[i]
def markValue (i : Fin 3) (length : Word) : Word := if i=0 then length+4 else if i=1 then 8 else 18

theorem mark (i : Fin 3) (s : State) (kind key length out written : Word) (bytes : Array UInt8) (frame : List Region)
    (hi : HeaderInv s kind key length out written bytes frame) :
    ∃ t, AccessTrace program 0 [] [] 1 (atPC s (markPC i)) t ∧ t.pc=markPC i+4 ∧
      HeaderInv t kind key length out written bytes frame ∧ t.getReg .x5=markValue i length := by
  rcases hi with ⟨hk,hkey,hl,ho,hw,hra,hm,hvalid⟩
  have cases_i : i=0 ∨ i=1 ∨ i=2 := by have := i.isLt; omega
  rcases cases_i with rfl | rfl | rfl
  all_goals
    simp only [markPC]
    refine ⟨?_,?trace,?post⟩
    case trace =>
      parser_access_step
      exact .nil _
    case post => simp_all [HeaderInv,markPC,markValue,getReg_setReg]

end Libp2pAsm.Refinement.Identity.Peer
