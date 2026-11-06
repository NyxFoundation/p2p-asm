import Tests.Certificate.Support

namespace Libp2pAsm.Tests.Certificate
open Rv64
open AsmCrypto (check snapshot)

private def runCase (dir : System.FilePath) (code : Array Instr) (i : Nat) : IO Unit := do
  let c ← HashCrypto.loadCase dir i
  let label ← IO.FS.readFile (dir / s!"case-{i}" / "label.txt")
  let .ok want := reference c | throw (IO.userError s!"invalid fixture {label}")
  check s!"{label}: Python status agrees with Spec" (want.status == c.field 0)
  let oracle ← IO.FS.readBinFile (dir / s!"case-{i}" / "expected.bin")
  check s!"{label}: independent complete expected snapshot"
    (oracle == snapshot (expected c want))
  let p : Program := ⟨0x10000, code⟩
  let (remaining, done, coverage) ← match checkedRun p c want 2000000 c.start
      (Array.replicate code.size 0) with
    | .error reason => throw (IO.userError s!"{label}: {reason}")
    | .ok result => pure result
  IO.FS.writeBinFile (dir / s!"case-{i}" / "after.bin") (snapshot done)
  check s!"{label}: exact registers, guards, output, work/stack wipes"
    (snapshot done == oracle && done.pc == 0x80000)
  let count := 2000000-remaining
  check s!"{label}: advertised engineering instruction bound"
    (count ≤ 20000+50*c.a.size+5000*(arg c 7))
  IO.FS.writeFile (dir / s!"case-{i}" / "count.txt") s!"{count}"
  IO.FS.writeBinFile (dir / s!"case-{i}" / "coverage.bin") ⟨coverage⟩
  IO.println s!"PASS {label}: {count} instructions"

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: Certificate-Probe artifact-directory")
  let dir : System.FilePath := directory
  let .ok body := Asm.Identity.X509.certificate | throw (IO.userError "certificate linking")
  let .ok code := body.lower | throw (IO.userError "certificate lowering")
  let .ok bytes := encodeProgram code | throw (IO.userError "certificate encoding")
  IO.FS.writeFile (dir / "protocol.S") (Codegen.assembly code)
  IO.FS.writeBinFile (dir / "encoded.bin") bytes
  let text ← IO.FS.readFile (dir / "count.txt")
  let some count := text.trimAscii.toString.toNat? | throw (IO.userError "fixture count")
  check "bounded nonempty fixture list" (0 < count && count < 10000)
  for i in List.range count do runCase dir code i

end Libp2pAsm.Tests.Certificate
