import Tests.AsmCrypto.Support
import Tests.AsmCrypto.Trace

namespace Libp2pAsm.Tests.AsmCrypto

open Rv64 Asm.Crypto.Sha2

def emit (v : Variant) (dir : System.FilePath) : IO (Array Instr) := do
  let body := match v with
    | .sha256 => Asm.Crypto.SHA256.compress
    | .sha512 => Asm.Crypto.SHA512.compress
  let .ok code := body.lower | throw (IO.userError "SAsm validation failed")
  let .ok bytes := encodeProgram code | throw (IO.userError "encoding failed")
  IO.FS.writeFile (dir / "protocol.S") (Codegen.assembly code)
  IO.FS.writeBinFile (dir / "encoded.bin") bytes
  IO.FS.writeBinFile (dir / "constants.bin") ⟨constants v⟩
  check "emit exactly four bytes per typed instruction" (bytes.size == 4 * code.size)
  return code

def caseTest (v : Variant) (code : Array Instr) (dir : System.FilePath)
    (case : Nat) (state block : Array UInt8) : IO (Nat × Array Event) := do
  let start := initial v case state block
  let .ok done := runUntil ⟨0x10000, code⟩ 0x18000 20000 start
    | throw (IO.userError s!"case {case}: execution trapped or exhausted fuel")
  let want := expected v start state block
  check s!"match compress, guards, wipes and all registers in case {case}"
    (snapshot done.state == snapshot want && done.state.pc == want.pc)
  let .error .fuelExhausted := runUntil ⟨0x10000, code⟩ 0x18000 (done.steps - 1) start
    | throw (IO.userError "instruction-count boundary was not exact")
  IO.FS.writeBinFile (dir / s!"case-{case}.before.bin") (snapshot start)
  IO.FS.writeBinFile (dir / s!"case-{case}.after.bin") (snapshot done.state)
  let .ok events := trace ⟨0x10000, code⟩ done.steps start
    | throw (IO.userError "trace execution failed")
  check s!"access only owned payloads in case {case}"
    (events.all (footprint v.rounds (2*v.width) (case % 8)))
  return (done.steps, events)

def run (v : Variant) (dir : System.FilePath) : IO Unit := do
  let code ← emit v dir
  let cases ← IO.FS.readBinFile (dir / "cases.bin")
  let stride := 64 + 2 * v.width
  check "accept only complete, bounded nonempty fixtures"
    (cases.size > 0 && cases.size % stride == 0 && cases.size / stride ≤ 4096)
  let mut counts : Array Nat := #[]
  let mut traces : Array (Array Event) := #[]
  for case in List.range (cases.size / stride) do
    let offset := case * stride
    let state := (cases.extract offset (offset + 64)).data
    let block := (cases.extract (offset + 64) (offset + stride)).data
    let (count, events) ← caseTest v code dir case state block
    counts := counts.push count
    if case < 8 then
      traces := traces.push events
      IO.FS.writeFile (dir / s!"alignment-{case}.trace.txt") (reprStr events)
    else
      check s!"preserve the public control/access trace in case {case}"
        (events == traces[case % 8]!)
  check "measure equal step counts over these fixtures" (counts.all (· == counts[0]!))
  IO.FS.writeFile (dir / "measurements.txt")
    s!"static_instructions={code.size}\ndynamic_instructions={counts[0]!}\ncases={counts.size}\ntrace_groups=8\n"
  IO.println s!"PASS {repr v}: {counts.size} model cases; {code.size} static / {counts[0]!} executed instructions"

end Libp2pAsm.Tests.AsmCrypto

def main (args : List String) : IO Unit := do
  match args with
  | ["sha256", dir] => Libp2pAsm.Tests.AsmCrypto.run .sha256 dir
  | ["sha512", dir] => Libp2pAsm.Tests.AsmCrypto.run .sha512 dir
  | _ => throw (IO.userError "usage: Probe.lean {sha256|sha512} artifact-directory")
