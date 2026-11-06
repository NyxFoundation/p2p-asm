import Tests.RSA.Support

namespace Libp2pAsm.Tests.RSA
open Rv64

def run (kind : String) (dir : System.FilePath) : IO Unit := do
  check "unknown RSA scheme" (kind == "pkcs" || kind == "pss")
  let usePSS := kind == "pss"
  let .ok stmt := Asm.Crypto.RSA.verify usePSS | throw (IO.userError "link failed")
  let .ok code := stmt.lower | throw (IO.userError "lower failed")
  let .ok bytes := encodeProgram code | throw (IO.userError "encode failed")
  IO.FS.writeFile (dir/"protocol.S") (Codegen.assembly code)
  IO.FS.writeBinFile (dir/"encoded.bin") bytes
  let .ok json := Lean.Json.parse (← IO.FS.readFile (dir/"cases.json"))
    | throw (IO.userError "invalid JSON")
  let fs ← match Lean.fromJson? (α := Array Fixture) json with
    | .ok fs => pure fs | .error e => throw (IO.userError e)
  let mut measurements := s!"static_instructions={code.size}\n"
  for idx in List.range fs.size do
    let f := fs[idx]!
    check "invalid fixture sizes" (f.regions.size == 6 && f.args.size ≤ 8 &&
      f.regions.all (fun r => r.size > 0 && r.size ≤ 65536 && r.all (· < 256)))
    if f.checkSpec then
      let bs := fun (a : Array Nat) => (a.map Nat.toUInt8).toList
      let scheme := if usePSS then Spec.Crypto.RSA.Scheme.pssRsaeSha256 else .pkcs1Sha256
      check s!"{f.label}: spec" ((Spec.Crypto.RSA.verify scheme 2048
        (bs f.n) (bs f.e) (bs f.digest) (bs f.signature)) == (f.status == 0))
    let start := initial f
    let want := expected f start
    let budget := Asm.Crypto.RSA.workBound f.n.size f.e.size
    check "program mapping" ((Program.mk 0x10000 code).valid start.memory)
    let done ← match checkedLoop ⟨0x10000,code⟩ f budget start 0 with
      | .ok d => pure d | .error e => throw (IO.userError s!"{f.label}: {e}")
    IO.FS.writeBinFile (dir/s!"case-{idx}.before.bin") (snapshot start)
    IO.FS.writeBinFile (dir/s!"case-{idx}.after.bin") (snapshot done.state)
    IO.FS.writeBinFile (dir/s!"case-{idx}.expected.bin") (snapshot want)
    check s!"{f.label}: snapshot, status {done.state.getReg .x10 |>.toNat}, want {f.status}"
      (snapshot done.state == snapshot want)
    check s!"{f.label}: cost" (done.steps < budget)
    measurements := measurements ++ s!"{idx} {f.label} {done.steps} bound={budget}\n"
    IO.println s!"PASS {kind}/{f.label}: {done.steps} steps"
    (← IO.getStdout).flush
  IO.FS.writeFile (dir/"measurements.txt") measurements

def main (args : List String) : IO Unit := do
  match args with
  | [kind,dir] => run kind dir
  | _ => throw (IO.userError "usage: rsa-probe pkcs|pss directory")

end Libp2pAsm.Tests.RSA
