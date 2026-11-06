import Tests.Identity.Support

namespace Libp2pAsm.Tests.Identity.Native
open Rv64
open AsmCrypto (check snapshot)

private def runCase (kind : String) (dir : System.FilePath)
    (code : Array Instr) (i : Nat) : IO Unit := do
  let c ← HashCrypto.loadCase dir i
  let .ok want := reference kind c | throw (IO.userError "invalid fixture or reference failure")
  check "independent metadata/spec status and exact owned sizes agree"
    (want.status == c.field 0 && want.wipe == c.field 1 && want.depth == c.field 2)
  let p : Program := ⟨0x10000, code⟩
  let .ok done := runUntil p 0x80000 (5000+600*c.a.size) c.start
    | throw (IO.userError s!"{kind} case {i}: trap or instruction budget")
  check s!"{kind} case {i}: complete Spec memory/register/wipe snapshot"
    (snapshot done.state == snapshot (expected c want) && done.state.pc == 0x80000)
  let .ok events := AsmCrypto.trace p done.steps c.start
    | throw (IO.userError "identity trace failed")
  check "exact input/output/work/frame footprint, no guard or early access"
    (events.all (permitted kind c want))
  IO.FS.writeBinFile (dir / s!"case-{i}" / "after.bin") (snapshot done.state)
  IO.println s!"PASS {kind} case {i}: {done.steps} instructions"

def run (kind : String) (dir : System.FilePath) : IO Unit := do
  let body ← match kind with
    | "publickey" => match Asm.Identity.PublicKey.decode with
      | .ok s => pure s | .error e => throw (IO.userError e)
    | "peerid" => pure Asm.Identity.PublicKey.peerId
    | "varint" => pure Asm.Codec.ProtobufVarint.decode
    | _ => throw (IO.userError "unknown operation")
  let .ok code := body.lower | throw (IO.userError "identity lowering failed")
  let .ok binary := encodeProgram code | throw (IO.userError "identity encoding failed")
  IO.FS.writeFile (dir / "protocol.S") (Codegen.assembly code)
  IO.FS.writeBinFile (dir / "encoded.bin") binary
  let countText ← IO.FS.readFile (dir / "count.txt")
  let some count := countText.trimAscii.toString.toNat?
    | throw (IO.userError "invalid fixture count")
  check "bounded nonempty fixture set" (0 < count && count < 10000)
  for i in List.range count do runCase kind dir code i

end Libp2pAsm.Tests.Identity.Native

def main (args : List String) : IO Unit := do
  match args with
  | [kind, dir] => Libp2pAsm.Tests.Identity.Native.run kind dir
  | _ => throw (IO.userError "usage: Identity-Probe publickey|peerid|varint artifact-directory")
