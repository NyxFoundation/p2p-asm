import Tests.Isa.Fixture
import Libp2pAsm.Codegen.X64

open Libp2pAsm

def main (args : List String) : IO UInt32 := do
  if args == ["--help"] then
    IO.println "Usage: libp2p-asm-isa-probe [--target x86_64] asm <instruction> | (asm|hex) <instruction> | eval <instruction> <u64> <u64>"
    return 0
  if let ["eval", name, a, b] := args then
    let some bytes := Tests.Isa.evaluate name a b | return 2
    IO.println (Codegen.hexBytes bytes)
    return 0
  if let ["--target", "x86_64", "asm", name] := args then
    let some code := Tests.Isa.program name | return 2
    let .ok text := Codegen.X64.assembly code | return 1
    IO.print text
    return 0
  let [format, name] := args | return 2
  let some code := Tests.Isa.program name | return 2
  if format == "asm" then IO.print (Codegen.assembly code); return 0
  if format == "hex" then
    let .ok bytes := Rv64.encodeProgram code | return 1
    IO.println (Codegen.hexBytes bytes)
    return 0
  return 2
