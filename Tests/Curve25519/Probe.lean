import Tests.Curve25519.Support

namespace Libp2pAsm.Tests.Curve25519
open Rv64
open AsmCrypto (check snapshot)

private def one (kind : String) (dir : System.FilePath) (code : Array Instr) (i : Nat) : IO Unit := do
  let c ← HashCrypto.loadCase dir i
  if c.field 0 >= 9 then
    check "reject invalid semantic input in independent Spec" (match reference kind c with | .error _ => true | .ok _ => false)
  let result ← if c.field 0 == 0 then match reference kind c with
    | .ok r => pure r | .error e => throw (IO.userError e)
    else pure #[]
  let done ← match runUntil ⟨0x10000,code⟩ 0x80000 30000000 c.start with
    | .ok result => pure result
    | .error e => throw (IO.userError s!"execution {kind} {i}: {repr e}")
  let path := dir / s!"case-{i}"
  IO.FS.writeBinFile (path / "after.bin") (snapshot done.state)
  check s!"match Spec/registers/guards/wipes {kind} {i}"
    (snapshot done.state == snapshot (expected c result))
  if c.field 4 == 1 then
    let other := changed c
    let .ok actual := tracePair ⟨0x10000,code⟩ c done.steps c.start other.start
      | throw (IO.userError s!"trace mismatch {kind} {i}")
    let result₂ ← if c.field 0 == 0 then match reference kind other with
      | .ok r => pure r | .error e => throw (IO.userError e)
      else pure #[]
    check "changed secret result" (snapshot actual == snapshot (expected other result₂))
  IO.FS.writeFile (path / "steps.txt") s!"{done.steps}\n"
  IO.println s!"PASS {kind} case {i}: {done.steps} steps"

def run (kind : String) (dir : System.FilePath) : IO Unit := do
  let stmt ← match body kind with
    | .ok s => pure s | .error e => throw (IO.userError e)
  let .ok code := stmt.lower | throw (IO.userError "SAsm validation")
  let .ok bytes := encodeProgram code | throw (IO.userError "encode failed")
  IO.FS.writeFile (dir / "protocol.S") (Codegen.assembly code)
  IO.FS.writeBinFile (dir / "encoded.bin") bytes
  IO.println s!"{kind}: {code.size} typed instructions"
  let countText ← IO.FS.readFile (dir / "count.txt")
  let some count := countText.trimAscii.toString.toNat? | throw (IO.userError "case count")
  check "bounded fixture count" (0 < count && count < 2048)
  for i in List.range count do one kind dir code i

end Libp2pAsm.Tests.Curve25519

def main (args : List String) : IO Unit := match args with
  | [kind, dir] => Libp2pAsm.Tests.Curve25519.run kind dir
  | _ => throw (IO.userError "usage: Probe.lean algorithm artifact-directory")
