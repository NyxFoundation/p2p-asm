import Tests.QuicCrypto.Observe

namespace Libp2pAsm.Tests.QuicCrypto
open Rv64
open AsmCrypto (check snapshot)

def result (kind : String) (c : HashCrypto.Case) : IO (Array UInt8) := do
  if c.field 0 == 0 then
    match reference kind c with | .ok r => pure r | .error e => throw (IO.userError e)
  else
    if c.field 0 == 6 || (c.field 0 == 2 && c.field 1 > 0) then
      check "independent Spec rejects processed invalid input" (match reference kind c with | .error _ => true | .ok _ => false)
    return #[]

private def one (kind : String) (dir : System.FilePath) (code : Array Instr) (i : Nat) : IO Unit := do
  let c ← HashCrypto.loadCase dir i
  let answer ← result kind c
  let path := dir / s!"case-{i}"
  let name ← IO.FS.readFile (path / "name.txt")
  let fuel := 500000+100000*(c.a.size/16+c.b.size/16+1)
  let done ← match runUntil ⟨0x10000,code⟩ 0x80000 fuel c.start with
    | .ok r => pure r | .error e => throw (IO.userError s!"execution {kind} {name}: {repr e}")
  IO.FS.writeBinFile (path / "after.bin") (snapshot done.state)
  check s!"Spec/registers/guards/wipes {kind} {name}: status {done.state.getReg .x10}"
    (snapshot done.state == snapshot (expected c answer))
  if (kind == "seal" || kind == "open") && (name == "rfc-client" || name == "rfc-server") then
    let sample ← IO.FS.readBinFile (path / "sample.bin")
    let mask ← IO.FS.readBinFile (path / "mask.bin")
    let address := (if kind == "open" then 0x200008+c.field 5 else 0x400008+1600)+c.field 7+4
    let .ok () := observeHP ⟨0x10000,code⟩ address sample.data mask.data done.steps c.start 0
      | throw (IO.userError s!"RFC HP intermediate {name}")
  if c.field 4 == 1 then
    let alt ← HashCrypto.loadCase (dir / "alternate") i
    let .ok actual := tracePair ⟨0x10000,code⟩ c done.steps c.start alt.start
      | throw (IO.userError s!"trace mismatch {kind} {name}")
    let other ← result kind alt
    IO.FS.writeBinFile (dir / "alternate" / s!"case-{i}" / "after.bin") (snapshot actual)
    check s!"alternate Spec/snapshot {kind} {name}" (snapshot actual == snapshot (expected alt other))
  IO.FS.writeFile (path / "steps.txt") s!"{done.steps}\n"
  IO.println s!"PASS {kind} {name}: {done.steps} steps"

def run (kind : String) (dir : System.FilePath) : IO Unit := do
  let stmt ← match body kind with | .ok s => pure s | .error e => throw (IO.userError e)
  let .ok code := stmt.lower | throw (IO.userError "SAsm validation")
  let .ok bytes := encodeProgram code | throw (IO.userError "encode failed")
  IO.FS.writeFile (dir / "protocol.S") (Codegen.assembly code)
  IO.FS.writeBinFile (dir / "encoded.bin") bytes
  IO.println s!"{kind}: {code.size} typed instructions"
  let countText ← IO.FS.readFile (dir / "count.txt")
  let some count := countText.trimAscii.toString.toNat? | throw (IO.userError "case count")
  check "bounded fixture count" (0 < count && count < 4096)
  for i in List.range count do one kind dir code i

end Libp2pAsm.Tests.QuicCrypto

def main (args : List String) : IO Unit := match args with
  | [kind,dir] => Libp2pAsm.Tests.QuicCrypto.run kind dir
  | _ => throw (IO.userError "usage: quicProbe operation artifact-directory")
