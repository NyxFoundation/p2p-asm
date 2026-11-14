import Libp2pAsm.Rv64.Vocabulary
import LeanAsm.Frontend

/-!
The deliberately small instruction profile used by p2p-asm's existing
exhaustive proofs. Instructions are the shared `LeanAsm.Rv64.Instr`
constructors narrowed by `isaProfile`; widening the profile is an explicit
p2p proof change rather than an accidental consequence of LeanAsm adding
instructions.
-/

namespace Libp2pAsm.Rv64

/-- The shared portable instruction type, restricted by `isaProfile` for
local programs. Accepting a new opcode is an explicit p2p proof change.

`check` rejects instructions outside the profile instead of silently widening
the accepted set when LeanAsm grows. -/
abbrev Instr : Type := LeanAsm.Rv64.Instr

/-- The exact opcode policy currently used by p2p execution and proofs. -/
def isaProfile : LeanAsm.Rv64.IsaProfile :=
  ⟨[.ADD, .SUB, .AND, .OR, .XOR, .SLL, .SRL, .SRA, .SLT, .SLTU,
    .ADDI, .ANDI, .ORI, .XORI, .SLLI, .SRLI, .SRAI, .LUI, .AUIPC,
    .MUL, .MULHU, .DIVU, .REMU, .LBU, .LD, .SB, .SD,
    .BEQ, .BNE, .BLTU, .BGEU, .JAL, .JALR]⟩

/-- Reject instructions outside `isaProfile` instead of widening the accepted
set by accident. -/
private def check (code : List Instr) : Except String (List Instr) :=
  if code.all isaProfile.supports then .ok code
  else .error "instruction is outside the p2p-asm ISA profile"

theorem check_conforms (code : List Instr)
    (h : (check code).isOk) :
    LeanAsm.Rv64.Program.Conforms isaProfile code := by
  unfold check at h
  split at h
  case isTrue hc =>
    intro target membership
    have hs := List.all_eq_true.mp hc target membership
    exact (LeanAsm.Rv64.IsaProfile.supports_eq_true isaProfile target).mp hs
  case isFalse =>
    simp only [Except.isOk, Except.toBool, Bool.false_eq_true] at h

instance : LeanAsm.LowerRv64 (List Instr) where
  lower code := check code

instance : LeanAsm.LowerRv64 (Array Instr) where
  lower code := check code.toList

instance : LeanAsm.EmitAsm (List Instr) where
  emit name code := do
    let _ ← LeanAsm.lowerRv64 code
    return LeanAsm.Rv64.emitProgram name code

instance : LeanAsm.EmitAsm (Array Instr) where
  emit name code := do
    let _ ← LeanAsm.lowerRv64 code
    return LeanAsm.Rv64.emitProgram name code.toList

end Libp2pAsm.Rv64
