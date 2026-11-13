import Libp2pAsm.Rv64.Vocabulary
import LeanAsm.Frontend

/-!
The deliberately small instruction profile used by p2p-asm's existing
exhaustive proofs. The embedding into LeanAsm is total; widening this profile is
an explicit p2p proof change rather than an accidental consequence of LeanAsm
adding instructions.
-/

namespace Libp2pAsm.Rv64

inductive Instr where
  | ADD (rd rs1 rs2 : Reg) | SUB (rd rs1 rs2 : Reg)
  | AND (rd rs1 rs2 : Reg) | OR (rd rs1 rs2 : Reg) | XOR (rd rs1 rs2 : Reg)
  | SLL (rd rs1 rs2 : Reg) | SRL (rd rs1 rs2 : Reg) | SRA (rd rs1 rs2 : Reg)
  | SLT (rd rs1 rs2 : Reg) | SLTU (rd rs1 rs2 : Reg)
  | ADDI (rd rs1 : Reg) (imm : BitVec 12)
  | ANDI (rd rs1 : Reg) (imm : BitVec 12)
  | ORI (rd rs1 : Reg) (imm : BitVec 12)
  | XORI (rd rs1 : Reg) (imm : BitVec 12)
  | SLLI (rd rs1 : Reg) (shamt : BitVec 6)
  | SRLI (rd rs1 : Reg) (shamt : BitVec 6)
  | SRAI (rd rs1 : Reg) (shamt : BitVec 6)
  | LUI (rd : Reg) (imm : BitVec 20)
  | AUIPC (rd : Reg) (imm : BitVec 20)
  | MUL (rd rs1 rs2 : Reg) | MULHU (rd rs1 rs2 : Reg)
  | DIVU (rd rs1 rs2 : Reg) | REMU (rd rs1 rs2 : Reg)
  | LBU (rd rs1 : Reg) (offset : BitVec 12)
  | LD (rd rs1 : Reg) (offset : BitVec 12)
  | SB (rs1 rs2 : Reg) (offset : BitVec 12)
  | SD (rs1 rs2 : Reg) (offset : BitVec 12)
  | BEQ (rs1 rs2 : Reg) (offset : BitVec 13)
  | BNE (rs1 rs2 : Reg) (offset : BitVec 13)
  | BLTU (rs1 rs2 : Reg) (offset : BitVec 13)
  | BGEU (rs1 rs2 : Reg) (offset : BitVec 13)
  | JAL (rd : Reg) (offset : BitVec 21)
  | JALR (rd rs1 : Reg) (offset : BitVec 12)
  deriving DecidableEq, BEq, Repr

namespace Instr

def toLeanAsm : Instr → LeanAsm.Rv64.Instr
  | .ADD d a b => .ADD d a b
  | .SUB d a b => .SUB d a b
  | .AND d a b => .AND d a b
  | .OR d a b => .OR d a b
  | .XOR d a b => .XOR d a b
  | .SLL d a b => .SLL d a b
  | .SRL d a b => .SRL d a b
  | .SRA d a b => .SRA d a b
  | .SLT d a b => .SLT d a b
  | .SLTU d a b => .SLTU d a b
  | .ADDI d a n => .ADDI d a n
  | .ANDI d a n => .ANDI d a n
  | .ORI d a n => .ORI d a n
  | .XORI d a n => .XORI d a n
  | .SLLI d a n => .SLLI d a n
  | .SRLI d a n => .SRLI d a n
  | .SRAI d a n => .SRAI d a n
  | .LUI d n => .LUI d n
  | .AUIPC d n => .AUIPC d n
  | .MUL d a b => .MUL d a b
  | .MULHU d a b => .MULHU d a b
  | .DIVU d a b => .DIVU d a b
  | .REMU d a b => .REMU d a b
  | .LBU d a n => .LBU d a n
  | .LD d a n => .LD d a n
  | .SB a b n => .SB a b n
  | .SD a b n => .SD a b n
  | .BEQ a b n => .BEQ a b n
  | .BNE a b n => .BNE a b n
  | .BLTU a b n => .BLTU a b n
  | .BGEU a b n => .BGEU a b n
  | .JAL d n => .JAL d n
  | .JALR d a n => .JALR d a n

end Instr

/-- The exact opcode policy currently used by p2p execution and proofs. -/
def isaProfile : LeanAsm.Rv64.IsaProfile :=
  ⟨[.ADD, .SUB, .AND, .OR, .XOR, .SLL, .SRL, .SRA, .SLT, .SLTU,
    .ADDI, .ANDI, .ORI, .XORI, .SLLI, .SRLI, .SRAI, .LUI, .AUIPC,
    .MUL, .MULHU, .DIVU, .REMU, .LBU, .LD, .SB, .SD,
    .BEQ, .BNE, .BLTU, .BGEU, .JAL, .JALR]⟩

@[simp] theorem Instr.toLeanAsm_supported (instruction : Instr) :
    isaProfile.Supports instruction.toLeanAsm := by
  cases instruction <;>
    simp [isaProfile, Instr.toLeanAsm, LeanAsm.Rv64.IsaProfile.Supports,
      LeanAsm.Rv64.Instr.opcode]

instance : LeanAsm.LowerRv64 (List Instr) where
  lower code := .ok (code.map Instr.toLeanAsm)

instance : LeanAsm.LowerRv64 (Array Instr) where
  lower code := .ok (code.toList.map Instr.toLeanAsm)

instance : LeanAsm.EmitAsm (List Instr) where
  emit name code := .ok (LeanAsm.Rv64.emitProgram name (code.map Instr.toLeanAsm))

instance : LeanAsm.EmitAsm (Array Instr) where
  emit name code :=
    .ok (LeanAsm.Rv64.emitProgram name (code.toList.map Instr.toLeanAsm))

end Libp2pAsm.Rv64
