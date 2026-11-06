import Std

/-!
Register names and the typed instruction representation are adapted from
RiscvZkvm.Rv64.Basic at afcbc45e1c74c2d296e032b5606dd977a304e8ad,
originally from evm-asm. See LICENSES/ and docs/provenance.md.
Only the implemented instruction subset is represented; no zkVM operations.
-/

namespace Libp2pAsm.Rv64

abbrev Word := BitVec 64

inductive Reg where
  | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7
  | x8 | x9 | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x18 | x19 | x20 | x21 | x22 | x23
  | x24 | x25 | x26 | x27 | x28 | x29 | x30 | x31
  deriving DecidableEq, BEq, Repr

def Reg.toNat : Reg → Nat
  | .x0 => 0 | .x1 => 1 | .x2 => 2 | .x3 => 3
  | .x4 => 4 | .x5 => 5 | .x6 => 6 | .x7 => 7
  | .x8 => 8 | .x9 => 9 | .x10 => 10 | .x11 => 11
  | .x12 => 12 | .x13 => 13 | .x14 => 14 | .x15 => 15
  | .x16 => 16 | .x17 => 17 | .x18 => 18 | .x19 => 19
  | .x20 => 20 | .x21 => 21 | .x22 => 22 | .x23 => 23
  | .x24 => 24 | .x25 => 25 | .x26 => 26 | .x27 => 27
  | .x28 => 28 | .x29 => 29 | .x30 => 30 | .x31 => 31

theorem Reg.toNat_lt (r : Reg) : r.toNat < 32 := by
  cases r <;> decide

def Reg.toFin (r : Reg) : Fin 32 := ⟨r.toNat, r.toNat_lt⟩

instance : ToString Reg := ⟨fun r => s!"x{r.toNat}"⟩

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

inductive Trap where
  | memoryBounds | memoryMisaligned | readOnlyMemory | invalidMemory
  | instructionBounds | instructionMisaligned | invalidProgram
  | unsupportedWidth | fuelExhausted
  deriving DecidableEq, BEq, Repr

end Libp2pAsm.Rv64
