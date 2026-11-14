import Libp2pAsm.Rv64.Profile
import LeanAsm.X64.Symbolic

namespace Libp2pAsm.Codegen.X64

open LeanAsm.X64

/-- Internal code addresses retain RV64 byte offsets, independently of native layout. -/
def codeBase : Nat := 0x10000

def pcLabel (index : Nat) : String := s!"_p2p_pc_{index}"

def lines (code : List Instr) : Symbolic.Program := code.map .instr

def slot (reg : Rv64.Reg) : Address := .base .r12 (BitVec.ofNat 32 (8 * reg.toNat))

def load (dst : Reg) (src : Rv64.Reg) : Instr :=
  if src == .x0 then .movImm .b64 dst 0 else .mov .b64 dst (.mem (slot src))

def save (dst : Rv64.Reg) (src : Reg := .rax) : List Instr :=
  if dst == .x0 then [] else [.store .b64 (slot dst) src]

private def binary (op : AluOp) (d a b : Rv64.Reg) : List Instr :=
  [load .rax a, load .rcx b, .alu op .b64 .rax (.reg .rcx)] ++ save d

private def immediate (op : AluOp) (d a : Rv64.Reg) (value : BitVec 12) : List Instr :=
  [load .rax a, .aluImm op .b64 .rax (value.signExtend 32)] ++ save d

private def shift (op : ShiftOp) (d a b : Rv64.Reg) : List Instr :=
  [load .rax a, load .rcx b, .shift op .b64 .rax .cl] ++ save d

private def shiftImmediate (op : ShiftOp) (d a : Rv64.Reg) (n : BitVec 6) : List Instr :=
  [load .rax a, .shift op .b64 .rax (.imm (n.zeroExtend 8))] ++ save d

private def compare (cond : Cond) (d a b : Rv64.Reg) : List Instr :=
  [load .rax a, load .rcx b, .alu .cmp .b64 .rax (.reg .rcx),
   .setcc cond .rax, .extend false .b8 .b64 .rax (.reg .rax)] ++ save d

private def readMemory (size : Size) (d a : Rv64.Reg) (off : BitVec 12) : List Instr :=
  [load .rcx a,
   if size == .b8 then .extend false .b8 .b64 .rax (.mem (.base .rcx (off.signExtend 32)))
   else .mov .b64 .rax (.mem (.base .rcx (off.signExtend 32)))] ++ save d

private def writeMemory (size : Size) (a b : Rv64.Reg) (off : BitVec 12) : List Instr :=
  [load .rcx a, load .rax b, .store size (.base .rcx (off.signExtend 32)) .rax]

private def multiply (high : Bool) (d a b : Rv64.Reg) : List Instr :=
  [load .rax a, load .rcx b, .mul false .b64 (.reg .rcx)] ++
    save d (if high then .rdx else .rax)

private def divide (index : Nat) (remainder : Bool) (d a b : Rv64.Reg) : Symbolic.Program :=
  let zero := s!"_p2p_div_zero_{index}"
  let done := s!"_p2p_div_done_{index}"
  lines [load .rax a, load .rcx b, .alu .test .b64 .rcx (.reg .rcx)] ++
  [.branch .e zero] ++
  lines [.movImm .b64 .rdx 0, .div false .b64 (.reg .rcx)] ++
  (if remainder then lines [.mov .b64 .rax (.reg .rdx)] else []) ++
  [.jump done, .label zero] ++
  (if remainder then [] else lines [.movImm .b64 .rax (-1)]) ++
  [.label done] ++ lines (save d)

private def arithmetic (index : Nat) : Rv64.Instr → Option Symbolic.Program
  | .ADD d a b => some (lines (binary .add d a b))
  | .SUB d a b => some (lines (binary .sub d a b))
  | .AND d a b => some (lines (binary .bitAnd d a b))
  | .OR d a b => some (lines (binary .bitOr d a b))
  | .XOR d a b => some (lines (binary .bitXor d a b))
  | .SLL d a b => some (lines (shift .shl d a b))
  | .SRL d a b => some (lines (shift .shr d a b))
  | .SRA d a b => some (lines (shift .sar d a b))
  | .SLT d a b => some (lines (compare .l d a b))
  | .SLTU d a b => some (lines (compare .b d a b))
  | .ADDI d a n => some (lines (immediate .add d a n))
  | .ANDI d a n => some (lines (immediate .bitAnd d a n))
  | .ORI d a n => some (lines (immediate .bitOr d a n))
  | .XORI d a n => some (lines (immediate .bitXor d a n))
  | .SLLI d a n => some (lines (shiftImmediate .shl d a n))
  | .SRLI d a n => some (lines (shiftImmediate .shr d a n))
  | .SRAI d a n => some (lines (shiftImmediate .sar d a n))
  | .LUI d n => some (lines ([.movImm .b64 .rax (n.signExtend 64 <<< 12)] ++ save d))
  | .AUIPC d n => some (lines ([.movImm .b64 .rax
      (BitVec.ofNat 64 (codeBase + 4 * index) + (n.signExtend 64 <<< 12))] ++ save d))
  | .MUL d a b => some (lines (multiply false d a b))
  | .MULHU d a b => some (lines (multiply true d a b))
  | .DIVU d a b => some (divide index false d a b)
  | .REMU d a b => some (divide index true d a b)
  | .LBU d a off => some (lines (readMemory .b8 d a off))
  | .LD d a off => some (lines (readMemory .b64 d a off))
  | .SB a b off => some (lines (writeMemory .b8 a b off))
  | .SD a b off => some (lines (writeMemory .b64 a b off))
  | _ => none

private def target (count index : Nat) (offset : Int) : Except String String := do
  let address := Int.ofNat (4 * index) + offset
  unless address ≥ 0 && address ≤ Int.ofNat (4 * count) && address % 4 == 0 do
    throw "x86-64: branch target is outside the program or not instruction-aligned"
  return pcLabel (address.toNat / 4)

private def branch (count index : Nat) (cond : Cond) (a b : Rv64.Reg)
    (off : BitVec 13) : Except String Symbolic.Program := do
  return lines [load .rax a, load .rcx b, .alu .cmp .b64 .rax (.reg .rcx)] ++
    [.branch cond (← target count index off.toInt)]

def instruction (count index : Nat) (instr : Rv64.Instr) : Except String Symbolic.Program := do
  if let some code := arithmetic index instr then return code
  match instr with
  | .BEQ a b off => branch count index .e a b off
  | .BNE a b off => branch count index .ne a b off
  | .BLTU a b off => branch count index .b a b off
  | .BGEU a b off => branch count index .ae a b off
  | .JAL d off =>
    return lines ([.movImm .b64 .rax (BitVec.ofNat 64 (codeBase + 4 * (index + 1)))] ++ save d) ++
      [.jump (← target count index off.toInt)]
  | .JALR d a off =>
    return lines ([load .rax a, .aluImm .add .b64 .rax (off.signExtend 32),
      .aluImm .bitAnd .b64 .rax (-2),
      .movImm .b64 .rcx (BitVec.ofNat 64 (codeBase + 4 * (index + 1)))] ++ save d .rcx) ++
      [.jump "_p2p_dispatch"]
  | _ => throw "x86-64: instruction is outside the p2p-asm ISA profile"

end Libp2pAsm.Codegen.X64
