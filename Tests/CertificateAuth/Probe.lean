import Tests.CertificateAuth.Support
import Tests.CertificateAuth.Trace
import Tests.CertificateAuth.SpecTests
import Libp2pAsm.Asm.Identity.Certificate.Authenticate
import Libp2pAsm.Asm.Identity.Certificate.Sign
import Libp2pAsm.Asm.Identity.Certificate.Issue

namespace Libp2pAsm.Tests.CertificateAuth
open Rv64
open Spec.Identity.Certificate

def program (kind : String) : Except String SAsm.Stmt := match kind with
  | "auth" => Asm.Identity.Certificate.authenticate
  | "cv-verify" => Asm.Identity.Certificate.verifyCV
  | "cv-sign" => Asm.Identity.Certificate.signCV
  | "issue" => Asm.Identity.Certificate.Issue.issue
  | _ => .error "unknown certificate operation"

def reference (kind : String) (f : Fixture) : Except Error (List UInt8) := do
  let raw := f.raw.toList.map Nat.toUInt8
  let digest := f.digest.toList.map Nat.toUInt8
  let policy : Policy := ⟨raw.length, raw.length, raw.length, raw.length, 2048⟩
  match kind with
  | "auth" =>
    let result ← authenticate policy [raw] f.role f.utcNs (f.expectedPeer.toList.map Nat.toUInt8)
    return result.peerId
  | "cv-verify" =>
    verifyCV policy raw f.scheme f.role digest (f.signature.toList.map Nat.toUInt8)
    return []
  | "cv-sign" => signCV (f.seed.toList.map Nat.toUInt8) f.role digest
  | "issue" =>
    let result ← issue f.hostKind (f.host.toList.map Nat.toUInt8)
      (f.seed.toList.map Nat.toUInt8) f.notBefore f.notAfter
    return result.der
  | _ => throw .length

def one (kind : String) (dir : System.FilePath) (code : Array Instr)
    (idx : Nat) (f : Fixture) : IO Unit := do
  if f.checkSpec then
    let result := reference kind f
    let status := match result with | .ok _ => 0 | .error e => e.code
    check s!"{f.label}: pure Spec status {status}, expected {f.specStatus}" (status == f.specStatus)
    if let .ok bytes := result then
      check s!"{f.label}: pure Spec value" (bytes.toArray == f.result.map Nat.toUInt8)
  let start := initial f
  let want := expected f start
  check "program mapping" ((Program.mk 0x10000 code).valid start.memory)
  let done ← match checkedLoop ⟨0x10000,code⟩ f f.budget start 0 with
    | .ok d => pure d | .error e => throw (IO.userError s!"{f.label}: {e}")
  IO.FS.writeBinFile (dir/s!"case-{idx}.before.bin") (snapshot start)
  IO.FS.writeBinFile (dir/s!"case-{idx}.after.bin") (snapshot done.state)
  IO.FS.writeBinFile (dir/s!"case-{idx}.expected.bin") (snapshot want)
  check s!"{f.label}: snapshot, status {done.state.getReg .x10 |>.toNat}, want {f.outputs}"
    (snapshot done.state == snapshot want)
  IO.FS.writeFile (dir/s!"case-{idx}.steps.txt") s!"{done.steps}\n"
  IO.println s!"PASS {kind}/{f.label}: {done.steps} steps"

def run (kind : String) (dir : System.FilePath) (traced : Bool := false) : IO Unit := do
  let stmt ← match program kind with | .ok s => pure s | .error e => throw (IO.userError e)
  let code ← match stmt.lower with
    | .ok c => pure c | .error e => throw (IO.userError s!"lower: {repr e}")
  let .ok bytes := encodeProgram code | throw (IO.userError "encode")
  IO.FS.writeFile (dir/"protocol.S") (Codegen.assembly code)
  IO.FS.writeBinFile (dir/"encoded.bin") bytes
  IO.println s!"{kind}: {code.size} instructions"
  let .ok json := Lean.Json.parse (← IO.FS.readFile (dir/"cases.json"))
    | throw (IO.userError "JSON")
  let fs ← match Lean.fromJson? (α := Array Fixture) json with
    | .ok fs => pure fs | .error e => throw (IO.userError e)
  if !traced then
    for idx in List.range fs.size do one kind dir code idx fs[idx]!
  else
    check "exactly two trace cases" (fs.size == 2)
    let (a,b) ← match tracePair ⟨0x10000,code⟩ fs[0]! fs[1]! fs[0]!.budget
        (initial fs[0]!) (initial fs[1]!) 0 with
      | .ok pair => pure pair | .error e => throw (IO.userError e)
    for (done,idx) in [(a,0),(b,1)] do
      let f := fs[idx]!
      let start := initial f
      let want := expected f start
      let .ok result := reference kind f | throw (IO.userError "trace Spec failure")
      check "trace Spec result" (result.toArray == f.result.map Nat.toUInt8)
      check "trace full snapshot" (snapshot done.state == snapshot want)
      IO.FS.writeBinFile (dir/s!"case-{idx}.before.bin") (snapshot start)
      IO.FS.writeBinFile (dir/s!"case-{idx}.after.bin") (snapshot done.state)
      IO.FS.writeBinFile (dir/s!"case-{idx}.expected.bin") (snapshot want)
      IO.FS.writeFile (dir/s!"case-{idx}.steps.txt") s!"{done.steps}\n"
    IO.println s!"PASS {kind}: equal PCs/addresses for {a.steps} actual instructions"

def main (args : List String) : IO Unit := match args with
  | [kind,dir] => run kind dir
  | ["trace",kind,dir] => run kind dir true
  | _ => throw (IO.userError "usage: certificate-auth-probe operation directory")

end Libp2pAsm.Tests.CertificateAuth
