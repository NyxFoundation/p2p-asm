import Tests.HashCrypto.Trace

namespace Libp2pAsm.Tests.HashCrypto
open Rv64
open AsmCrypto (check snapshot)

private def emit (kind : String) (dir : System.FilePath) : IO (Array Instr) := do
  let stmt ← match body kind with
    | .ok s => pure s | .error e => throw (IO.userError e)
  let .ok code := stmt.lower | throw (IO.userError "SAsm validation failed")
  let .ok bytes := encodeProgram code | throw (IO.userError "encode failed")
  IO.FS.writeFile (dir / "protocol.S") (Codegen.assembly code)
  IO.FS.writeBinFile (dir / "encoded.bin") bytes
  if kind == "sha256" || kind == "sha512" then
    let v := variant kind
    let .ok compression := (Asm.Crypto.Sha2.compress v).lower
      | throw (IO.userError "compression lowering failed")
    check "retain original compression instruction counts"
      (compression.size == if kind == "sha256" then 230 else 197)
    let .ok original := encodeProgram compression | throw (IO.userError "compression encoding")
    IO.FS.writeBinFile (dir / "compression.bin") original
  IO.FS.writeBinFile (dir / "constants.bin") ⟨AsmCrypto.constants (variant kind)⟩
  IO.println s!"{kind}: {code.size} typed instructions; checked SAsm and call relocations"
  return code

private def runCase (kind : String) (dir : System.FilePath) (code : Array Instr)
    (i : Nat) : IO Unit := do
  let c ← loadCase dir i
  let result ← if c.field 0 == 0 then
      match reference kind c with
      | .ok r => pure r | .error e => throw (IO.userError e)
    else pure #[]
  let done ← match runUntil ⟨0x10000, code⟩ 0x80000 20000000 c.start with
    | .ok d => pure d | .error e => throw (IO.userError s!"{kind} case {i}: {repr e}")
  let path := dir / s!"case-{i}"
  IO.FS.writeBinFile (path / "after.bin") (snapshot done.state)
  let want := expected c result
  check s!"match Spec, all registers, guards and exact wipes: {kind} case {i}"
    (snapshot done.state == snapshot want && done.state.pc == want.pc)
  if c.field 4 == 1 then
    let other := changed c
    let .ok traced := tracePair ⟨0x10000, code⟩ c done.steps c.start other.start
      | throw (IO.userError s!"{kind} case {i}: public trace/footprint differs")
    let result₂ ← if c.field 0 == 0 then
        match reference kind other with
        | .ok r => pure r | .error e => throw (IO.userError e)
      else pure #[]
    check "match the independently specified changed-content result"
      (snapshot traced == snapshot (expected other result₂))
  IO.FS.writeFile (path / "steps.txt") s!"{done.steps}\n"
  IO.println s!"PASS {kind} case {i}: {done.steps} model steps"

def run (kind : String) (dir : System.FilePath) : IO Unit := do
  let code ← emit kind dir
  let countText ← IO.FS.readFile (dir / "count.txt")
  let some count := countText.trimAscii.toString.toNat? | throw (IO.userError "case count")
  check "bound fixture count" (count > 0 && count < 1024)
  for i in List.range count do runCase kind dir code i

end Libp2pAsm.Tests.HashCrypto

def main (args : List String) : IO Unit := do
  match args with
  | [kind, dir] => Libp2pAsm.Tests.HashCrypto.run kind dir
  | _ => throw (IO.userError "usage: Probe.lean algorithm artifact-directory")
