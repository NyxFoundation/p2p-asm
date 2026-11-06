import Libp2pAsm.Codegen.Assembly
import Libp2pAsm.Codegen.Input
import Libp2pAsm.Rv64.Execution

namespace Libp2pAsm.Tests.Isa

open Rv64

def instructions : List (String × Instr) := [
  ("add", .ADD .x12 .x10 .x11), ("sub", .SUB .x12 .x10 .x11),
  ("and", .AND .x12 .x10 .x11), ("or", .OR .x12 .x10 .x11), ("xor", .XOR .x12 .x10 .x11),
  ("sll", .SLL .x12 .x10 .x11), ("srl", .SRL .x12 .x10 .x11), ("sra", .SRA .x12 .x10 .x11),
  ("slt", .SLT .x12 .x10 .x11), ("sltu", .SLTU .x12 .x10 .x11),
  ("addi", .ADDI .x12 .x10 (-2048)), ("andi", .ANDI .x12 .x10 (-2048)),
  ("ori", .ORI .x12 .x10 (-1)), ("xori", .XORI .x12 .x10 (-1)),
  ("slli", .SLLI .x12 .x10 63), ("srli", .SRLI .x12 .x10 63),
  ("srai", .SRAI .x12 .x10 63), ("lui", .LUI .x12 0x80000),
  ("auipc", .AUIPC .x12 0xfffff), ("mul", .MUL .x12 .x10 .x11),
  ("mulhu", .MULHU .x12 .x10 .x11), ("divu", .DIVU .x12 .x10 .x11),
  ("remu", .REMU .x12 .x10 .x11), ("lbu", .LBU .x12 .x10 0), ("ld", .LD .x12 .x10 0),
  ("sb", .SB .x10 .x11 0), ("sd", .SD .x10 .x11 0),
  ("beq", .BEQ .x10 .x11 12), ("bne", .BNE .x10 .x11 12),
  ("bltu", .BLTU .x10 .x11 12), ("bgeu", .BGEU .x10 .x11 12),
  ("jal", .JAL .x12 8), ("jalr", .JALR .x12 .x10 12)]

def program (name : String) : Option (Array Instr) := do
  let (_, instruction) ← instructions.find? (fun entry => entry.1 == name)
  let suffix := #[.ADDI .x10 .x12 0, .ADDI .x12 .x8 0, .JALR .x0 .x1 0]
  let body := match instruction with
    | .BEQ .. | .BNE .. | .BLTU .. | .BGEU .. =>
      #[instruction, .ADDI .x12 .x0 1, .JAL .x0 8, .ADDI .x12 .x0 2]
    | .JAL .. => #[instruction, .ADDI .x12 .x0 99]
    | .JALR .. => #[instruction, .ADDI .x12 .x0 99, .ADDI .x12 .x0 99]
    | .SB .. => #[instruction, .LBU .x12 .x10 0]
    | .SD .. => #[instruction, .LD .x12 .x10 0]
    | _ => #[instruction]
  return body ++ suffix

def dataBytes (name : String) (b : Word) : ByteArray :=
  Codegen.wordBytes [if name == "sb" || name == "sd" then ~~~b else b, 0xa5a5a5a5a5a5a5a5]

def evaluate (name a b : String) : Option ByteArray := do
  let code ← program name
  let lhs ← Codegen.parseWord a
  let rhs ← Codegen.parseWord b
  let memory : Memory :=
    { regions := #[{ base := 0x20000, bytes := (dataBytes name rhs).data, writable := true }] }
  let s : State := { pc := 0x10000, memory := memory }
  let pointer := ["lbu", "ld", "sb", "sd"].contains name
  let first := if pointer then 0x20000 else if name == "jalr" then 0x10001 else lhs
  let input := ((s.setReg .x10 first).setReg .x11 rhs).setReg .x8 0x11223344
  let done ← (runUntil { base := 0x10000, code := code } 0 16 input).toOption
  let bytes := Codegen.wordBytes ([.x10, .x11, .x12].map done.state.getReg)
  let region ← done.state.memory.regions[0]?
  return bytes ++ ⟨region.bytes⟩

end Libp2pAsm.Tests.Isa
