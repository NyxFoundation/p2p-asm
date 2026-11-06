import Libp2pAsm.Spec.Identity.X509.Algorithm
import Libp2pAsm.Asm.Identity.X509.Algorithm
import Tests.CertificateTime.Support

namespace Libp2pAsm.Tests.CertificateAlgorithms.Native
open Rv64
open AsmCrypto (check snapshot)
open CertificateTime.Native (Outcome word span expected)

private def reference (kind : String) (c : HashCrypto.Case) : Except String Outcome := do
  if !span (word c .x10) (word c .x11) then return { status := 4 }
  unless c.a.size == word c .x11 do throw "algorithm fixture length mismatch"
  let parsed := if kind == "signature" then Spec.Identity.X509.signatureAlgorithm c.a.toList
    else Spec.Identity.X509.publicKeyAlgorithm c.a.toList
  match parsed with
  | .error _ => return { status := 8 }
  | .ok kind => return { status := 0, value := kind }

private def permitted (c : HashCrypto.Case) (o : Outcome) (e : AsmCrypto.Event) : Bool :=
  match e.access with
  | none => true
  | some (write, width, addr) => o.status != 4 && !write && width == 1 &&
    word c .x10 ≤ addr.toNat && addr.toNat+1 ≤ word c .x10+c.a.size

private def runCase (kind : String) (dir : System.FilePath)
    (code : Array Instr) (i : Nat) : IO Unit := do
  let c ← HashCrypto.loadCase dir i
  let .ok want := reference kind c | throw (IO.userError "invalid algorithm fixture")
  check "independent algorithm oracle agrees with Spec"
    (want.status == c.field 0 && want.value == c.field 1)
  let p : Program := ⟨0x10000, code⟩
  let .ok done := runUntil p 0x80000 5000 c.start
    | throw (IO.userError s!"{kind} case {i}: trap or instruction budget")
  check s!"{kind} case {i}: exact registers and unchanged memory"
    (snapshot done.state == snapshot (expected c want) && done.state.pc == 0x80000)
  let .ok events := AsmCrypto.trace p done.steps c.start
    | throw (IO.userError "algorithm trace failed")
  check "read-only body footprint, no metadata error access"
    (events.all (permitted c want))
  IO.FS.writeBinFile (dir / s!"case-{i}" / "after.bin") (snapshot done.state)
  IO.println s!"PASS {kind} case {i}: {done.steps} instructions"

def run (kind : String) (dir : System.FilePath) : IO Unit := do
  let body ← match kind with
    | "signature" => pure Asm.Identity.X509.Algorithm.signature
    | "public" => pure Asm.Identity.X509.Algorithm.publicKey
    | _ => throw (IO.userError "unknown algorithm operation")
  let .ok code := body.lower | throw (IO.userError "algorithm lowering failed")
  let .ok binary := encodeProgram code | throw (IO.userError "algorithm encoding failed")
  IO.FS.writeFile (dir / "protocol.S") (Codegen.assembly code)
  IO.FS.writeBinFile (dir / "encoded.bin") binary
  let text ← IO.FS.readFile (dir / "count.txt")
  let some count := text.trimAscii.toString.toNat?
    | throw (IO.userError "invalid fixture count")
  check "bounded nonempty fixture set" (0 < count && count < 10000)
  for i in List.range count do runCase kind dir code i

end Libp2pAsm.Tests.CertificateAlgorithms.Native

def main (args : List String) : IO Unit := do
  match args with
  | [kind, dir] => Libp2pAsm.Tests.CertificateAlgorithms.Native.run kind dir
  | _ => throw (IO.userError "usage: Algorithms-Probe signature|public artifact-directory")
