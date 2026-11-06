import Tests.Tls.Support
import Tests.Tls.Roundtrip

namespace Libp2pAsm.Tests.Tls
open Rv64 AsmCrypto

def one (kind : String) (dir : System.FilePath) (code : Array Instr) (i : Nat) : IO Unit := do
  let c ← HashCrypto.loadCase dir i
  let path := dir / s!"case-{i}"
  let name ← IO.FS.readFile (path / "name.txt")
  let answer ← if c.field 0 == 0 then match reference kind c with
    | .ok b => pure b | .error e => throw (IO.userError e)
    else pure #[]
  if c.field 4 == 1 then
    let verdict := verdict kind c
    let status := match verdict with | .ok _ => 0 | .error e => e.code
    check s!"Spec error class {name}: {status} versus {c.field 0}" (status == c.field 0)
  if kind == "decode" && c.field 8 == 1 && c.field 0 == 0 then
    let consumed := (readLE answer 8).toNat
    if readLE answer 440 == 0 then
      check s!"typed constructor roundtrip {name}" (match reencode c.a with | .ok b => b == c.a.extract 0 consumed | .error _ => false)
    else
      check s!"ClientHello emitter rejects SNI {name}" (match reencode c.a with | .error e => e == .profile | .ok _ => false)
  check "program mapping and disjoint code" ((Program.mk 0x10000 code).valid c.start.memory)
  let (actual,steps) ← match execute ⟨0x10000,code⟩ c (5000000+50000*c.a.size/64) c.start 0 with
    | .ok r => pure r | .error e => throw (IO.userError s!"{kind} {name}: {e}")
  IO.FS.writeBinFile (path / "after.bin") (snapshot actual)
  check s!"Spec/snapshot/wipes {kind} {name}, status={actual.getReg .x10}"
    (snapshot actual == snapshot (expected c answer))
  check s!"operation admission budget {name}" (steps ≤ budget kind c)
  let altPath := dir / "alternate" / s!"case-{i}"
  if ← (altPath / "before.bin").pathExists then
    let alt ← HashCrypto.loadCase (dir / "alternate") i
    let other ← match reference kind alt with
      | .ok r => pure r | .error e => throw (IO.userError e)
    let next ← match tracePair ⟨0x10000,code⟩ c steps c.start alt.start with
      | .ok s => pure s | .error e => throw (IO.userError s!"{name}: {e}")
    check s!"alternate complete snapshot {name}" (snapshot next == snapshot (expected alt other))
    IO.FS.writeBinFile (altPath / "after.bin") (snapshot next)
  IO.FS.writeFile (path / "steps.txt") s!"{steps}\n"
  IO.println s!"PASS {kind} {name}: {steps} instructions"

def run (kind : String) (dir : System.FilePath) : IO Unit := do
  let stmt ← match body kind with | .ok s => pure s | .error e => throw (IO.userError e)
  let .ok code := stmt.lower | throw (IO.userError "lower")
  let .ok bytes := encodeProgram code | throw (IO.userError "encode")
  IO.FS.writeFile (dir / "protocol.S") (Codegen.assembly code)
  IO.FS.writeBinFile (dir / "encoded.bin") bytes
  let countText ← IO.FS.readFile (dir / "count.txt")
  let some count := countText.trimAscii.toString.toNat? | throw (IO.userError "count")
  for i in List.range count do one kind dir code i

end Libp2pAsm.Tests.Tls

def main (args : List String) : IO Unit := match args with
  | [kind,dir] => Libp2pAsm.Tests.Tls.run kind dir
  | _ => throw (IO.userError "usage: tlsProbe operation artifact-directory")
