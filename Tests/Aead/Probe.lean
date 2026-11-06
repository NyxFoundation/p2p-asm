import Tests.Aead.Support
import Libp2pAsm.Refinement.Crypto.GCM.Bounds

namespace Libp2pAsm.Tests.Aead
open Rv64

/-- Full snapshot tests include untouched bytes and all ABI registers. -/
def caseTest (kind : String) (code : Array Instr) (f : Fixture) (dir : System.FilePath)
    (i : Nat) : IO (Nat × Array AsmCrypto.Event) := do
  validateFixture f
  let start := initial kind f
  let .ok done := runUntil ⟨0x10000, code⟩ 0x80000 5000000 start
    | throw (IO.userError s!"{kind}/{f.label}: trapped or fuel exhausted")
  let want := expectedState kind f start
  if kind == "seal" || kind == "open" then
    let messageLength := if kind == "open" then f.inputLength - 16 else f.inputLength
    let bound := if f.status == 0 || f.status == 6 then
      Refinement.Crypto.GCM.fuelBudget messageLength f.aadLength else 128
    check "fit the documented public-length fuel budget" (done.steps ≤ bound)
  IO.FS.writeBinFile (dir / s!"case-{i}.before.bin") (snapshot start)
  IO.FS.writeBinFile (dir / s!"case-{i}.after.bin") (snapshot done.state)
  IO.FS.writeBinFile (dir / s!"case-{i}.expected.bin") (snapshot want)
  check s!"match oracle, guards, wipes and every register: {kind}/{f.label}"
    (snapshot done.state == snapshot want && done.state.pc == want.pc)
  let .ok events := AsmCrypto.trace ⟨0x10000, code⟩ done.steps start
    | throw (IO.userError "trace execution failed")
  check s!"avoid guard reads/writes: {kind}/{f.label}" (events.all (footprint kind f))
  return (done.steps, events)

def checkReference (kind : String) (f : Fixture) : IO Unit := do
  let expected := bytes f.expected
  let valid := f.status == 0
  if kind == "aes" && valid then
    let key : Spec.Crypto.AES.ExpandedKey := Vector.ofFn fun i => (bytes f.key)[i.val]!
    let output := (Spec.Crypto.AES.encryptExpanded key (Spec.Crypto.GCM.blockOf (bytes f.input))).toArray
    check "match independent pure AES" (output == expected.extract 0 16)
  if kind == "seal" && valid then
    check "match independent pure GCM seal" (Spec.Crypto.GCM.seal (bytes f.key)
      (bytes f.nonce) (bytes f.aad) (bytes f.input) == .ok (expected.extract 0 (f.input.size+16)))
  if kind == "open" && (valid || f.status == 6) then
    let result := Spec.Crypto.GCM.open (bytes f.key) (bytes f.nonce) (bytes f.aad) (bytes f.input)
    check "match independent pure GCM open" (result ==
      if valid then .ok (expected.extract 0 (f.input.size-16)) else .error .authenticationFailed)
  if kind == "expand" && valid then
    check "match independent pure AES schedule" ((Spec.Crypto.AES.expand
      (Spec.Crypto.GCM.blockOf (bytes f.key))).toArray == expected.extract 0 176)
  if kind == "sbox" then
    check "match independent field-inversion S-box" ((bytes f.output).map Spec.Crypto.AES.sbox == expected)
  if kind == "ghash" then
    check "match independent 128-bit GHASH" ((Spec.Crypto.GCM.fieldBytes (Spec.Crypto.GCM.mul
      (Spec.Crypto.GCM.readBE (bytes f.output) ^^^ Spec.Crypto.GCM.readBE (bytes f.input)) (Spec.Crypto.GCM.readBE (bytes f.key)))).toArray == expected)

def run (kind : String) (dir : System.FilePath) : IO Unit := do
  let .ok code := (program kind).lower | throw (IO.userError "SAsm validation failed")
  let .ok encoded := encodeProgram code | throw (IO.userError "encoding failed")
  IO.FS.writeFile (dir / "protocol.S") (Codegen.assembly code)
  IO.FS.writeBinFile (dir / "encoded.bin") encoded
  let .ok json := Lean.Json.parse (← IO.FS.readFile (dir / "cases.json"))
    | throw (IO.userError "invalid fixture JSON")
  let .ok fixtures := Lean.fromJson? (α := Array Fixture) json
    | throw (IO.userError "invalid fixture schema")
  check "bound fixture count" (fixtures.size > 0 && fixtures.size ≤ 4096)
  let mut groups : Array (String × Array AsmCrypto.Event) := #[]
  let mut measurements := s!"static_instructions={code.size}\n"
  for i in List.range fixtures.size do
    let f := fixtures[i]!
    checkReference kind f
    let (steps, events) ← caseTest kind code f dir i
    if f.traceGroup != "" then
      if let some (_, old) := groups.find? (fun (g, _) => g == f.traceGroup) then
        check s!"keep identical control/address trace for {f.traceGroup}" (old == events)
      else groups := groups.push (f.traceGroup, events)
    measurements := measurements ++ s!"{i} {f.label} {steps}\n"
    IO.println s!"PASS {kind}/{f.label}: {steps} instructions"
  IO.FS.writeFile (dir / "measurements.txt") measurements

end Libp2pAsm.Tests.Aead

def main (args : List String) : IO Unit := do
  match args with
  | [kind, dir] => Libp2pAsm.Tests.Aead.run kind dir
  | _ => throw (IO.userError "usage: Probe.lean routine artifact-directory")
