import Libp2pAsm.Refinement.Tls.Encoding

namespace Libp2pAsm.Refinement.Tls
open Rv64 Asm.Crypto.Util

/-- Semantic state after the real fixed-status and caller-register wipe prefix.
The definition names the actual instructions, rather than assuming an external
register-clearing oracle. Return/fetch are deliberately separate obligations. -/
def wipeState (s : State) (status : BitVec 12) : State :=
  ((Asm.Crypto.Sha2.cleared.filter (· != .x10)).foldl
    (fun t r => (t.setReg r 0).advance) ((s.setReg .x10 (status.signExtend 64)).advance))

private theorem execute_clears (rs : List Reg) (s : State) :
    execSequence (rs.map (fun r => LeanAsm.Rv64.Instr.ADDI r .x0 0)) s =
      .ok (rs.foldl (fun t r => (t.setReg r 0).advance) s) := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    change (execInstr (.ADDI r .x0 0) s).bind
      (fun t => execSequence (rs.map (fun r => LeanAsm.Rv64.Instr.ADDI r .x0 0)) t) = _
    have first : execInstr (.ADDI r .x0 0) s = .ok ((s.setReg r 0).advance) := by
      simp [execInstr, writeReg]
    rw [first]
    exact ih ((s.setReg r 0).advance)

private theorem execute_status_clears (rs : List Reg) (s : State) (status : BitVec 12) :
    execSequence (LeanAsm.Rv64.Instr.ADDI .x10 .x0 status :: rs.map (fun r => LeanAsm.Rv64.Instr.ADDI r .x0 0)) s =
      .ok (rs.foldl (fun t r => (t.setReg r 0).advance)
        ((s.setReg .x10 (status.signExtend 64)).advance)) := by
  change (execInstr (.ADDI .x10 .x0 status) s).bind
    (fun t => execSequence (rs.map (fun r => LeanAsm.Rv64.Instr.ADDI r .x0 0)) t) = _
  have first : execInstr (.ADDI .x10 .x0 status) s =
      .ok ((s.setReg .x10 (status.signExtend 64)).advance) := by simp [execInstr, writeReg]
  rw [first]
  exact execute_clears rs ((s.setReg .x10 (status.signExtend 64)).advance)

theorem execute_status_and_wipe (s : State) (status : BitVec 12) :
    execSequence (LeanAsm.Rv64.Instr.ADDI .x10 .x0 status :: clearTemps) s = .ok (wipeState s status) := by
  exact execute_status_clears (Asm.Crypto.Sha2.cleared.filter (· != .x10)) s status

/-- The entire straight-line success/failure exit prefix occurs in the ACTUAL
QUIC boundary leaf, followed immediately by the real JALR return. -/
theorem record_reject_path_in_leaf :
    (Asm.Tls.Codec.admitQuic.flatten.drop 1).take ((finish 3).size) = (finish 3).flatten := by decide

theorem keyupdate_reject_path_in_leaf :
    (Asm.Tls.Codec.admitQuic.flatten.drop ((finish 3).size+4)).take ((finish 3).size) =
      (finish 3).flatten := by decide

private theorem clears_preserve (rs : List Reg) (r : Reg) (s : State)
    (h : ∀ x ∈ rs, r.toNat ≠ x.toNat) :
    (rs.foldl (fun t x => (t.setReg x 0).advance) s).getReg r = s.getReg r := by
  induction rs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ih ((s.setReg x 0).advance) (by intro y hy; exact h y (by simp [hy]))]
    exact State.getReg_setReg_other s x r 0 (h x (by simp))

theorem wipe_preserves_saved (s : State) (status : BitVec 12) (r : Reg)
    (hr : r ∈ [.x1,.x2,.x3,.x4,.x8,.x9,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27]) :
    (wipeState s status).getReg r = s.getReg r := by
  unfold wipeState
  rw [clears_preserve]
  · apply State.getReg_setReg_other
    simp at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro x hx
    simp [Asm.Crypto.Sha2.cleared] at hx
    simp at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hx with ⟨hx,_⟩ <;>
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem clears_memory (rs : List Reg) (s : State) :
    (rs.foldl (fun t r => (t.setReg r 0).advance) s).memory = s.memory := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    rw [List.foldl_cons, ih]
    exact State.memory_setReg s r 0

theorem wipe_preserves_memory (s : State) (status : BitVec 12) :
    (wipeState s status).memory = s.memory := by
  unfold wipeState
  rw [clears_memory]
  exact State.memory_setReg s .x10 (status.signExtend 64)

theorem wipe_status (s : State) (status : BitVec 12) :
    (wipeState s status).getReg .x10 = status.signExtend 64 := by
  unfold wipeState
  rw [clears_preserve]
  · exact State.getReg_setReg_same s .x10 _ (by decide)
  · decide

end Libp2pAsm.Refinement.Tls
