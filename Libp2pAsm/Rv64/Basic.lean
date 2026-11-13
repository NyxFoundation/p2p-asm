import LeanAsm.Rv64.Basic

/-!
The shared word, register, and trap vocabulary now comes from LeanAsm. The
project-specific instruction subset remains local during the staged migration;
its exhaustive proofs intentionally continue to range over only implemented
instructions.
-/

namespace Libp2pAsm.Rv64

abbrev Word := LeanAsm.Rv64.Word
abbrev Reg := LeanAsm.Rv64.Reg

namespace Reg
export LeanAsm.Rv64.Reg (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)
export LeanAsm.Rv64.Reg (x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
export LeanAsm.Rv64.Reg (zero ra sp gp tp t0 t1 t2 s0 fp s1 a0 a1 a2 a3 a4 a5 a6 a7)
export LeanAsm.Rv64.Reg (s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
def toNat (reg : Reg) : Nat := LeanAsm.Rv64.Reg.toNat reg

theorem toNat_lt (reg : Reg) : reg.toNat < 32 := by
  simpa [toNat] using LeanAsm.Rv64.Reg.toNat_lt reg

def toFin (reg : Reg) : Fin 32 := ⟨reg.toNat, reg.toNat_lt⟩
end Reg

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

abbrev Trap := LeanAsm.Rv64.Trap

namespace Trap
export LeanAsm.Rv64.Trap (memoryBounds memoryMisaligned readOnlyMemory invalidMemory)
export LeanAsm.Rv64.Trap (instructionBounds instructionMisaligned invalidProgram)
export LeanAsm.Rv64.Trap (unsupportedWidth fuelExhausted)
end Trap

end Libp2pAsm.Rv64
