import Tests.CertificateTime.Support

namespace Libp2pAsm.Tests.CertificateTime.Native
open Rv64
open AsmCrypto (check snapshot)

private def runCase (kind : String) (dir : System.FilePath)
    (code : Array Instr) (i : Nat) : IO Unit := do
  let c ← HashCrypto.loadCase dir i
  let .ok want := reference kind c | throw (IO.userError "invalid time fixture")
  check "independent status and value agree with Spec"
    (want.status == c.field 0 && want.value == c.field 1)
  let p : Program := ⟨0x10000, code⟩
  let .ok done := runUntil p 0x80000 5000 c.start
    | throw (IO.userError s!"{kind} case {i}: trap or instruction budget")
  check s!"{kind} case {i}: complete memory/register snapshot"
    (snapshot done.state == snapshot (expected c want) && done.state.pc == 0x80000)
  let .ok events := AsmCrypto.trace p done.steps c.start
    | throw (IO.userError "time trace failed")
  check "exact byte footprint, no reads/writes on metadata errors"
    (events.all (permitted kind c want))
  IO.FS.writeBinFile (dir / s!"case-{i}" / "after.bin") (snapshot done.state)
  IO.println s!"PASS {kind} case {i}: {done.steps} instructions"

def run (kind : String) (dir : System.FilePath) : IO Unit := do
  let body ← match kind with
    | "decode" => pure Asm.Identity.Time.decode
    | "encode" => pure Asm.Identity.Time.encode
    | "validity" => pure Asm.Identity.Time.validity
    | _ => throw (IO.userError "unknown time operation")
  let .ok code := body.lower | throw (IO.userError "time lowering failed")
  let .ok binary := encodeProgram code | throw (IO.userError "time encoding failed")
  IO.FS.writeFile (dir / "protocol.S") (Codegen.assembly code)
  IO.FS.writeBinFile (dir / "encoded.bin") binary
  let text ← IO.FS.readFile (dir / "count.txt")
  let some count := text.trimAscii.toString.toNat?
    | throw (IO.userError "invalid fixture count")
  check "bounded nonempty fixture set" (0 < count && count < 10000)
  for i in List.range count do runCase kind dir code i

end Libp2pAsm.Tests.CertificateTime.Native

def main (args : List String) : IO Unit := do
  match args with
  | [kind, dir] => Libp2pAsm.Tests.CertificateTime.Native.run kind dir
  | _ => throw (IO.userError "usage: Time-Probe decode|encode|validity artifact-directory")
