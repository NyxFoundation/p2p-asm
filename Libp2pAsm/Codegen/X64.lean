import Libp2pAsm.Codegen.X64.Instructions
import LeanAsm.ABI.SysVAMD64

namespace Libp2pAsm.Codegen.X64

open LeanAsm.X64

private def prologue (count : Nat) : Except Error Symbolic.Program := do
  return [.function "protocol_entry"] ++ lines (← LeanAsm.ABI.SysVAMD64.enter 8) ++
    lines [.mov .b64 .r12 (.reg .rdi), .movImm .b64 .rax 0,
      .store .b64 (slot .x0) .rax, load .rax .x1, .aluImm .bitAnd .b64 .rax (-2),
      .store .b64 (.base .rsp) .rax,
      .aluImm .sub .b64 .rax (BitVec.ofNat 32 codeBase),
      .aluImm .cmp .b64 .rax (BitVec.ofNat 32 (4 * count))] ++
    [.branch .b "_p2p_bad_pc"]

private def dispatch (count : Nat) : Symbolic.Program :=
  [.label (pcLabel count), .jump "_p2p_bad_pc", .label "_p2p_dispatch"] ++
  lines [.alu .cmp .b64 .rax (.mem (.base .rsp))] ++ [.branch .e "_p2p_return"] ++
  lines [.aluImm .sub .b64 .rax (BitVec.ofNat 32 codeBase),
    .aluImm .cmp .b64 .rax (BitVec.ofNat 32 (4 * count))] ++
  [.branch .ae "_p2p_bad_pc"] ++
  lines [.aluImm .test .b64 .rax 3] ++ [.branch .ne "_p2p_bad_pc"] ++
  lines [.shift .shr .b64 .rax (.imm 2)] ++ [.leaSymbol .rcx "_p2p_table"] ++
  lines [.extend true .b32 .b64 .rax (.mem (.indexed (some .rcx) .rax .four)),
    .alu .add .b64 .rax (.reg .rcx), .jmpReg .rax]

private def epilogue : Except Error Symbolic.Program := do
  return [.label "_p2p_bad_pc"] ++ lines [.movImm .b32 .rax 1] ++
    [.jump "_p2p_exit", .label "_p2p_return"] ++ lines [.movImm .b32 .rax 0] ++
    [.label "_p2p_exit"] ++ lines (← LeanAsm.ABI.SysVAMD64.leave 8) ++
    [.endFunction "protocol_entry"]

/-- GNU resolves signed relative table entries; there are no absolute text relocations. -/
private def table (count : Nat) : String :=
  ".section .rodata\n.p2align 2\n_p2p_table:\n" ++
    String.join ((List.range count).map fun i => s!"  .long {pcLabel i} - _p2p_table\n")

/-- Emit a System V AMD64 function taking a writable 32-word register context.
The context and its data/stack buffers must be disjoint. Internal code pointers
use `codeBase`; x1 is an out-of-image return sentinel. Memory pointers are native.
The native return value is 0 for return, 1 for an invalid control-flow target. -/
def assembly (code : Array Rv64.Instr) : Except String String := do
  unless !code.isEmpty && codeBase + 4 * code.size < 2 ^ 31 do
    throw "x86-64: empty program or program too large"
  let _ ← LeanAsm.lowerRv64 code
  let before ← (prologue code.size).mapError fun _ => "x86-64: invalid entry frame"
  let after ← epilogue.mapError fun _ => "x86-64: invalid exit frame"
  let body ← code.toList.zipIdx.flatMapM fun (instr, index) => do
    return .label (pcLabel index) :: (← instruction code.size index instr)
  -- All names are generated from disjoint prefixes and unique instruction indices.
  let emitted ← (before ++ body ++ dispatch code.size ++ after).mapM fun line =>
    (Symbolic.emitLine line).mapError fun _ => "x86-64: invalid generated operand"
  return assemblyHeader ++ String.intercalate "\n" emitted ++ "\n" ++
    table code.size ++ assemblyFooter

end Libp2pAsm.Codegen.X64
