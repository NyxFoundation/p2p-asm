import Libp2pAsm.Rv64.Execution
import Libp2pAsm.Rv64.SAsm

namespace Libp2pAsm.Tests.Machine

open Rv64

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL: {name}")

private def memoryChecks : IO Unit := do
  let region : Region := { base := 0x20000, bytes := #[1, 2, 3, 4, 5, 6, 7, 8], writable := true }
  let memory : Memory := { regions := #[region] }
  for width in [0, 3, 16] do
    check "should reject unsupported widths before alignment arithmetic"
      (match memory.load width 0x20000 with | .error .unsupportedWidth => true | _ => false)
  for (width, address, value) in [(2, 0x20002, 0x0403), (4, 0x20004, 0x08070605)] do
    check "should load every supported aligned width"
      (match memory.load width address with | .ok actual => actual == value | _ => false)
  let overlapping : Memory := { regions := #[region, { region with base := 0x20004 }] }
  check "should reject overlapping regions"
    (match overlapping.load 1 0x20000 with | .error .invalidMemory => true | _ => false)
  let wrapping : Memory := { regions := #[{ region with base := -4 }] }
  check "should reject a region that wraps the 64-bit address space"
    (match wrapping.load 1 (-4) with | .error .invalidMemory => true | _ => false)
  let short : Memory := { regions := #[{ region with bytes := #[1, 2, 3, 4, 5, 6, 7] }] }
  check "should reject a partially in-bounds wide load"
    (match short.load 8 0x20000 with | .error .memoryBounds => true | _ => false)
  check "should truncate stores to their width and preserve the other bytes"
    (match memory.store 1 0x20007 0x100 with
      | .ok result => match result.load 8 0x20000 with
        | .ok value => value == 0x0007060504030201 | _ => false
      | _ => false)

private def programChecks : IO Unit := do
  let p : Program := { base := 0x10000, code := #[.JALR .x0 .x1 0] }
  for address in [0xfffc, 0x10004] do
    check "should reject instruction fetch outside the exact code interval"
      (match p.fetch address with | .error .instructionBounds => true | _ => false)
  let writable : Memory :=
    { regions := #[{ base := 0x10000, bytes := #[0, 0, 0, 0], writable := true }] }
  check "should reject writable code aliases"
    (match runUntil p 0 1 { pc := 0x10000, memory := writable } with
      | .error .invalidProgram => true | _ => false)
  for bad in [({ base := 0x10002, code := p.code } : Program),
      { base := 0x10000, code := #[] },
      { base := -4, code := #[.ADDI .x10 .x0 0, .JALR .x0 .x1 0] }] do
    check "should reject misaligned, empty and wrapping program layouts" (!bad.valid {})
  let s : State := { pc := 0x10000 }
  check "should trap a taken misaligned control transfer"
    (match execInstr (.JAL .x0 2) s with | .error .instructionMisaligned => true | _ => false)
  check "should not trap an untaken branch for its unused target"
    (match execInstr (.BNE .x0 .x0 2) s with | .ok next => next.pc == 0x10004 | _ => false)

private def loweringChecks : IO Unit := do
  let nop : Instr := .ADDI .x0 .x0 0
  check "should reject hidden raw control flow inside a basic block"
    (match (SAsm.Stmt.block [.JAL .x0 4]).lower with | .error .controlInBlock => true | _ => false)
  let near := SAsm.Stmt.ite (.eq .x0 .x0) (.block (List.replicate 1021 nop)) (.block [])
  check "should allow the largest aligned positive short branch"
    (match near.lower with | .ok code => code.size == 1023 | _ => false)
  let far := SAsm.Stmt.ite (.eq .x0 .x0) (.block (List.replicate 1022 nop)) (.block [])
  check "should reject branch overflow before encoding wraps the offset"
    (match far.lower with | .error .branchOutOfRange => true | _ => false)
  let long := SAsm.Stmt.ite (.eq .x0 .x0) (.block []) (.block (List.replicate 262143 nop))
  check "should reject jump overflow before encoding wraps the offset"
    (match long.lower with | .error .jumpOutOfRange => true | _ => false)

def run : IO Unit := do
  memoryChecks
  programChecks
  loweringChecks
  IO.println "PASS: should enforce memory, fetch, control-flow and lowering boundaries"

end Libp2pAsm.Tests.Machine
