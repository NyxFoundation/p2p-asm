import Tests.Streams.Support
import Tests.Streams.ProofAudit
import Tests.Streams.SpecTests
import Libp2pAsm.Spec.Ping.Protocol
import Libp2pAsm.Spec.Multistream.Negotiation
import Libp2pAsm.Refinement.Stream.Arithmetic
import Libp2pAsm.Refinement.Stream.Id
import Libp2pAsm.Spec.Stream.Receive
import Libp2pAsm.Spec.Stream.Send
import Libp2pAsm.Asm.Stream.Receive
import Libp2pAsm.Asm.Stream.Send
import Libp2pAsm.Asm.Stream.Id
import Libp2pAsm.Spec.Stream.Id
import Libp2pAsm.Asm.Multistream.Negotiation
import Libp2pAsm.Asm.Ping.Protocol

namespace Libp2pAsm.Tests.Streams
open Rv64

def program (kind : String) : Except String SAsm.Stmt :=
  match kind with
  | "receive" => .ok Asm.Stream.receive
  | "consume" => .ok Asm.Stream.consume
  | "peek" => .ok Asm.Stream.peek
  | "append" => .ok Asm.Stream.append
  | "reserve" => .ok Asm.Stream.reserve
  | "settle" => .ok Asm.Stream.settle
  | "ack" => .ok Asm.Stream.acknowledge
  | "stop" => .ok Asm.Stream.stop
  | "negotiate" => Asm.Multistream.feed
  | "neg-emit" => .ok Asm.Multistream.emit
  | "neg-timer" => .ok Asm.Multistream.timer
  | "ping-begin" => .ok Asm.Ping.begin
  | "ping-feed" => .ok Asm.Ping.feed
  | "ping-release" => .ok Asm.Ping.release
  | "ping-finish" => .ok Asm.Ping.finish
  | "ping-cancel" => .ok (Asm.Ping.cancel false)
  | "ping-timer" => .ok (Asm.Ping.cancel true)
  | "ping-quota" => .ok Asm.Ping.quota
  | "ordinal" => .ok Asm.Stream.ordinal
  | "id" => .ok Asm.Stream.validateId
  | _ => .error "unknown leaf"

def run (kind : String) (dir : System.FilePath) : IO Unit := do
  let .ok stmt := program kind | throw (IO.userError "program")
  let code ← match stmt.lower with
    | .ok code => pure code
    | .error e => throw (IO.userError s!"lower: {repr e}")
  let .ok bytes := encodeProgram code | throw (IO.userError "encode")
  IO.FS.writeFile (dir/"protocol.S") (Codegen.assembly code)
  IO.FS.writeBinFile (dir/"encoded.bin") bytes
  let .ok json := Lean.Json.parse (← IO.FS.readFile (dir/"cases.json"))
    | throw (IO.userError "JSON")
  let fs ← match Lean.fromJson? (α := Array Fixture) json with
    | .ok fs => pure fs | .error e => throw (IO.userError e)
  let mut report := s!"static_instructions={code.size}\n"
  for idx in List.range fs.size do
    let f := fs[idx]!
    check "fixture" (f.regions.size == 6 && f.expectedRegions.size == 6 && f.args.size == 8)
    let start := initial f
    let want := expected f start
    check "program mapping" ((⟨0x10000, code⟩ : Program).valid start.memory)
    let (done, trace) ← match checkedLoop ⟨0x10000,code⟩ f f.budget start 0 #[] with
      | .ok d => pure d | .error e => throw (IO.userError s!"{f.label}: {e}")
    IO.FS.writeBinFile (dir/s!"case-{idx}.before.bin") (snapshot start)
    IO.FS.writeBinFile (dir/s!"case-{idx}.after.bin") (snapshot done.state)
    IO.FS.writeBinFile (dir/s!"case-{idx}.expected.bin") (snapshot want)
    IO.FS.writeBinFile (dir/s!"case-{idx}.accesses.bin") trace
    check s!"{f.label}: snapshot, status {done.state.getReg .x10 |>.toNat}, want {f.outputs}"
      (snapshot done.state == snapshot want)
    report := report ++ s!"{idx} {f.label}: {done.steps}/{f.budget}\n"
  IO.FS.writeFile (dir/"measurements.txt") report
  IO.println s!"PASS {kind}: {fs.size} snapshots, footprints, bounds"

def main (args : List String) : IO Unit := do
  match args with
  | ["spec"] => SpecTests.run
  | [kind,dir] => run kind dir
  | _ => throw (IO.userError "usage: streams-probe leaf directory")
end Libp2pAsm.Tests.Streams
