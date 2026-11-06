import Tests.Weierstrass.Trace

namespace Libp2pAsm.Tests.Weierstrass
open Rv64

def run (curve kind : String) (dir : System.FilePath) : IO Unit := do
  let c := if curve == "p256" then Spec.Crypto.Weierstrass.Curve.p256 else .secp256k1
  let .ok stmt := coreProgram c kind | throw (IO.userError "link failed")
  let .ok code := stmt.lower | throw (IO.userError "lower failed")
  let .ok encoded := encodeProgram code | throw (IO.userError "encode failed")
  IO.FS.writeFile (dir/"protocol.S") (Codegen.assembly code)
  IO.FS.writeBinFile (dir/"encoded.bin") encoded
  let .ok json := Lean.Json.parse (← IO.FS.readFile (dir/"cases.json"))
    | throw (IO.userError "invalid JSON")
  let fs ← match Lean.fromJson? (α := Array Fixture) json with
    | .ok fs => pure fs
    | .error e => throw (IO.userError s!"bad schema: {e}")
  let mut groups : Array (String × State) := #[]
  let mut measurements := s!"static_instructions={code.size}\n"
  for i in List.range fs.size do
    let f := fs[i]!
    check "invalid fixtures" (f.regions.size == 6 && f.args.size ≤ 8 &&
      f.regions.all (fun r => r.size > 0 && r.size ≤ 16384 && r.all (· < 256)))
    let start := initial f
    let want := expected f start
    if kind == "public" || kind == "ecdh" || kind.startsWith "sign" || kind.startsWith "verify" then
      reference c kind f
    let paired := (groups.find? (fun (g,_) => g == f.traceGroup)).map Prod.snd
    check "valid program/memory" ((Program.mk 0x10000 code).valid start.memory)
    let done ← match checkedLoop ⟨0x10000,code⟩ (accessContract kind f) 50000000 start paired 0 with
      | .ok done => pure done
      | .error e => throw (IO.userError s!"{f.label}: {e}")
    IO.FS.writeBinFile (dir/s!"case-{i}.before.bin") (snapshot start)
    IO.FS.writeBinFile (dir/s!"case-{i}.after.bin") (snapshot done.state)
    IO.FS.writeBinFile (dir/s!"case-{i}.expected.bin") (snapshot want)
    check s!"{f.label}: mismatch" (snapshot done.state == snapshot want)
    if f.traceGroup != "" && paired.isNone then groups := groups.push (f.traceGroup,start)
    measurements := measurements ++ s!"{i} {f.label} {done.steps} tracePair={paired.isSome}\n"
    IO.println s!"PASS {curve}/{kind}/{f.label}: {done.steps} steps"
  IO.FS.writeFile (dir/"measurements.txt") measurements

end Libp2pAsm.Tests.Weierstrass

def main (args : List String) : IO Unit := do
  match args with
  | [curve,kind,dir] => Libp2pAsm.Tests.Weierstrass.run curve kind dir
  | _ => throw (IO.userError "usage: Probe curve kind directory")
