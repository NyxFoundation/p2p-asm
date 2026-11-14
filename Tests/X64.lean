import Libp2pAsm.Codegen.X64

namespace Libp2pAsm.Tests.X64

open Rv64

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL: {name}")
  IO.println s!"PASS: {name}"

def run : IO Unit := do
  let emit := Codegen.X64.assembly
  check "should reject an empty x86 program" (!(emit #[]).isOk)
  check "should reject instructions outside the p2p ISA profile"
    (!(emit #[.ADDW .x10 .x10 .x11]).isOk)
  check "should reject a branch to a half-instruction"
    (!(emit #[.BEQ .x0 .x0 2, .JALR .x0 .x1 0]).isOk)
  check "should reject a branch before the program"
    (!(emit #[.BNE .x0 .x0 (-4), .JALR .x0 .x1 0]).isOk)
  check "should reject a jump beyond the program"
    (!(emit #[.JAL .x0 12, .JALR .x0 .x1 0]).isOk)
  check "should emit checked indirect jumps"
    ((emit #[.JALR .x10 .x10 (-1)]).isOk)

def fixtures : List (String × Array Instr) := [
  ("zero", #[.ADDI .x0 .x0 123, .ADD .x10 .x0 .x0, .JALR .x0 .x1 0]),
  ("alias", #[.SUB .x11 .x10 .x11, .SLL .x11 .x10 .x11,
    .MULHU .x10 .x10 .x11, .DIVU .x11 .x10 .x11, .JALR .x0 .x1 0]),
  ("offset", #[.LD .x10 .x10 (-8), .SD .x11 .x10 (-8),
    .LBU .x11 .x11 (-1), .JALR .x0 .x1 0]),
  ("indirect", #[.JALR .x10 .x10 0, .ADDI .x11 .x0 42, .JALR .x0 .x1 0]),
  ("fallthrough", #[.ADDI .x10 .x0 42]),
  ("endjump", #[.JAL .x0 4]),
  ("nested", #[.ADDI .x8 .x1 0, .AUIPC .x1 0, .ADDI .x1 .x1 12,
    .JAL .x0 12, .ADDI .x1 .x8 0, .JALR .x0 .x1 0,
    .ADDI .x9 .x1 0, .JAL .x1 12, .ADDI .x1 .x9 0, .JALR .x0 .x1 0,
    .ADDI .x10 .x10 1, .JALR .x0 .x1 0])]

def emitFixtures (directory : System.FilePath) : IO Unit := do
  run
  for (name, code) in fixtures do
    let .ok text := Codegen.X64.assembly code | throw (IO.userError "fixture emission failed")
    IO.FS.writeFile (directory / s!"{name}.S") text

end Libp2pAsm.Tests.X64
