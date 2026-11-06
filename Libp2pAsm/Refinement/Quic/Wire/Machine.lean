import Libp2pAsm.Asm.Quic.Wire.Permission
import Libp2pAsm.Asm.Quic.Wire.Writer
import Libp2pAsm.Rv64.Execution
import Libp2pAsm.Refinement.Registers
import Libp2pAsm.Refinement.Quic.Wire.Bounds

namespace Libp2pAsm.Refinement.Quic.Wire
open Rv64

/-- The first actual instruction of the checked take macro computes remaining
bytes; the natural-number interpretation follows from cursor <= source length. -/
theorem remaining_instruction (s : State) :
    execInstr (.SUB .x5 .x9 .x22) s =
      .ok ((s.setReg .x5 (s.getReg .x9-s.getReg .x22)).advance) := rfl

theorem remaining_word (length cursor : Nat) (h : cursor ≤ length) (hl : length < 2^64) :
    ((BitVec.ofNat 64 length)-(BitVec.ofNat 64 cursor)).toNat = length-cursor := by
  simp [BitVec.toNat_sub, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt (show cursor < 2^64 by omega)]
  omega

theorem successful_take_instructions (s : State) :
    execSequence [.ADDI .x11 .x22 0, .ADD .x22 .x22 .x10] s =
    .ok (((s.setReg .x11 (s.getReg .x22)).advance).setReg .x22
      (s.getReg .x22+s.getReg .x10)).advance := by
  simp [execSequence,execInstr,writeReg,bind,pure,Except.bind,Except.pure]
  rw [State.getReg_setReg_other s .x11 .x22 _ (by decide),
    State.getReg_setReg_other s .x11 .x10 _ (by decide)]

theorem reserve_advance_instruction (s : State) :
    execInstr (.ADD .x23 .x23 .x10) s =
    .ok ((s.setReg .x23 (s.getReg .x23+s.getReg .x10)).advance) := rfl

theorem reserve_word (used n capacity : Nat) (hu : used ≤ capacity)
    (hn : n ≤ capacity-used) (hc : capacity < 2^64) :
    ((BitVec.ofNat 64 used)+(BitVec.ofNat 64 n)).toNat = used+n := by
  have hsum : used+n < 2^64 := by omega
  simp [BitVec.toNat_add, Nat.mod_eq_of_lt hsum,
    Nat.mod_eq_of_lt (show used < 2^64 by omega), Nat.mod_eq_of_lt (show n < 2^64 by omega)]

/-- The actual ACK workspace immediate cannot wrap even at its maximum admitted count. -/
theorem ack_workspace_word (count : Nat) (h : count ≤ (2^64-145)/16) :
    ((BitVec.ofNat 64 count <<< 4)+(144 : Word)).toNat = 128+16*(count+1) := by
  have hc : count < 2^64 := by omega
  have hb := ack_workspace_nonwrapping count h
  simp [BitVec.toNat_add,BitVec.toNat_shiftLeft,Nat.mod_eq_of_lt hc]
  omega

/-- Reserved bits are zero in emitted long headers, independently of PN length. -/
theorem long_header_reserved (kind : Fin 3) (pn : Fin 4) :
    ((192+16*kind.val+pn.val) / 4) % 4 = 0 := by
  have hk := kind.isLt
  have hp := pn.isLt
  omega

theorem short_header_reserved (spin phase : Bool) (pn : Fin 4) :
    ((64+(if spin then 32 else 0)+(if phase then 4 else 0)+pn.val)/8)%4 = 0 := by
  cases spin <;> cases phase <;> have := pn.isLt <;> simp_all <;> omega

end Libp2pAsm.Refinement.Quic.Wire
