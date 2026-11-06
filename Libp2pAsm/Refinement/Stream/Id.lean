import Libp2pAsm.Asm.Stream.Id
import Libp2pAsm.Spec.Stream.Id
import Libp2pAsm.Rv64.Logic.Symbolic

namespace Libp2pAsm.Refinement.Stream
open Rv64 Rv64.Logic

/-- Mathematical ordinal extraction for every machine word, not finite samples. -/
theorem ordinal_shift (w : Word) : w >>> 2 = BitVec.ofNat 64 (w.toNat/4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  have h := w.isLt
  simp only [Nat.reducePow]
  omega

/-- Correspondence for the actual RV64 instruction used by both ID leaves. -/
theorem ordinal_instruction (s : State) :
    execInstr (.SRLI .x10 .x10 2) s =
      .ok (s.setReg .x10 (BitVec.ofNat 64 ((s.getReg .x10).toNat/4))).advance := by
  simp [execInstr, writeReg, ordinal_shift]

def ordinalCleared : List Reg := [.x11,.x12,.x13,.x14] ++ Asm.Stream.temps

def ordinalPost (s : State) : State :=
  ordinalCleared.foldl (fun t r => t.setReg r 0)
    (s.setReg .x10 (BitVec.ofNat 64 ((s.getReg .x10).toNat/4)))

/-- Whole straight-line body of the callable leaf, including register clearing.
The return/fetch obligations are stated separately below. -/
theorem ordinal_body (s : State) :
    execSequence (Asm.Stream.ordinal.flatten.take 15) s =
      .ok (atPC (ordinalPost s) (s.pc+60)) := by
  simp [Asm.Stream.ordinal, Asm.Stream.seq, Asm.sequence, Asm.Stream.b,
    Asm.Stream.exit, Asm.Stream.temps, SAsm.Stmt.flatten, execSequence,
    List.foldlM, execInstr, writeReg, advance_eq_atPC, getReg_setReg,
    ordinalPost, ordinalCleared, ordinal_shift, bind, Except.bind, pure, Except.pure]
  simp only [BitVec.add_assoc]
  rfl

/-- Full callable leaf execution, including JALR and all cleared temporaries.
A valid return mapping is a caller obligation; no memory is accessed. -/
theorem ordinal_leaf (s : State)
    (hret : ((s.getReg .x1) &&& (~~~(1 : Word))).toNat % 4 = 0) :
    execSequence Asm.Stream.ordinal.flatten s =
      .ok (atPC (ordinalPost s) ((s.getReg .x1) &&& (~~~(1 : Word)))) := by
  have code : Asm.Stream.ordinal.flatten =
      Asm.Stream.ordinal.flatten.take 15 ++ [.JALR .x0 .x1 0] := by rfl
  rw [code]
  simp only [execSequence, List.foldlM_append]
  change (do
    let t ← execSequence (Asm.Stream.ordinal.flatten.take 15) s
    execSequence [.JALR .x0 .x1 0] t) = _
  rw [ordinal_body]
  have hret' : ((s.getReg .x1).toNat &&& 18446744073709551614) % 4 = 0 := by simpa using hret
  simp [execSequence, List.foldlM, execInstr, jump_eq_atPC, hret', ordinalPost,
    ordinalCleared, Asm.Stream.temps, getReg_setReg, bind, Except.bind,
    pure, Except.pure]

/-- The poststate preserves the complete memory and callee register set. -/
theorem ordinal_memory (s : State) : (ordinalPost s).memory = s.memory := by
  simp [ordinalPost, ordinalCleared, Asm.Stream.temps]

theorem ordinal_value (s : State) :
    (ordinalPost s).getReg .x10 = BitVec.ofNat 64 ((s.getReg .x10).toNat/4) := by
  simp [ordinalPost, ordinalCleared, Asm.Stream.temps, getReg_setReg]

private theorem clear_frame (rs : List Reg) (s : State) (r : Reg) (h : r ∉ rs) :
    (rs.foldl (fun t w => t.setReg w 0) s).getReg r = s.getReg r := by
  induction rs generalizing s with
  | nil => rfl
  | cons w rs ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [List.foldl_cons]
    rw [ih _ h.2]
    by_cases hr : r = .x0
    · simp [hr]
    · simp [getReg_setReg, hr, h.1]

theorem ordinal_register_frame (s : State) (r : Reg)
    (h : r ∉ ordinalCleared) (ha : r ≠ .x10) :
    (ordinalPost s).getReg r = s.getReg r := by
  unfold ordinalPost
  rw [clear_frame _ _ _ h]
  by_cases hr : r = .x0
  · simp [hr]
  · simp [getReg_setReg, hr, ha]

theorem ordinal_lower : Asm.Stream.ordinal.lower = .ok Asm.Stream.ordinal.flatten.toArray := by
  rfl

end Libp2pAsm.Refinement.Stream
