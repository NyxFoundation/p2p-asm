import Tests.QuicWire.Support

namespace Libp2pAsm.Tests.QuicWire
open Rv64

def spec (kind : String) (bytes : Array UInt8) (option bound capacity : Nat) :
    Except Spec.Quic.Wire.Error (List UInt8) := do
  if kind == "packet" then return Spec.Quic.Wire.packWords (← Spec.Quic.Wire.parsePacket bytes option).words
  if kind == "frame" then return Spec.Quic.Wire.packWords (← Spec.Quic.Wire.parseFrame bytes bound).words
  if kind == "tp" then return Spec.Quic.Wire.packWords (← Spec.Quic.Wire.parseTransport bytes (option == 1) bound).words
  if kind.endsWith "-batch" then
    return Spec.Quic.Wire.packWords (← Spec.Quic.Wire.batchWords (kind == "packet-batch") bytes option bound)
  if kind.endsWith "-encode" then
    let k := if kind == "packet-encode" then 0 else if kind == "frame-encode" then 1 else 2
    return ← Spec.Quic.Wire.Descriptors.encode k bytes (option == 1) bound capacity
  throw ⟨10,bound⟩

def program (kind : String) : Except String SAsm.Stmt :=
  if kind == "packet" then Asm.Quic.Wire.packetParse else
  if kind == "frame" then Asm.Quic.Wire.frameParse else
  if kind == "tp" then Asm.Quic.Wire.transportParse else
  if kind == "packet-encode" then Asm.Quic.Wire.packetEncode else
  if kind == "frame-encode" then Asm.Quic.Wire.frameEncode else
  if kind == "tp-encode" then Asm.Quic.Wire.transportEncode else
  if kind == "permission" then Asm.Quic.Wire.framePermission else
  if kind.endsWith "-batch" then Asm.Quic.Wire.batchParse (kind == "packet-batch") else .error "unknown leaf"

def run (kind : String) (dir : System.FilePath) : IO Unit := do
  let stmt ← match program kind with
    | .ok s => pure s | .error e => throw (IO.userError e)
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
    if f.checkSpec then
      let bs := (f.regions[0]!.extract f.inputOffset (f.inputOffset+f.args[1]!)).map Nat.toUInt8
      match spec kind bs f.args[6]! f.args[7]! f.args[3]! with
      | .error e =>
        check s!"{f.label}: spec error {repr e}, expected {f.status}/{f.errorOffset}"
          (e.code == f.status && e.offset == f.errorOffset)
      | .ok words =>
        check s!"{f.label}: spec descriptor"
          (f.status == 0 && words == (f.output.map Nat.toUInt8).toList)
    let start := initial f
    let want := expected f start
    let budget := Asm.Quic.Wire.instructionBound kind code.size f.args[1]!
      f.args[6]! f.args[7]! f.args[3]! f.args[5]!
    check "program mapping" ((Program.mk 0x10000 code).valid start.memory)
    let done ← match checkedLoop ⟨0x10000,code⟩ f budget start 0 with
      | .ok d => pure d | .error e => throw (IO.userError s!"{f.label}: {e}")
    IO.FS.writeBinFile (dir/s!"case-{idx}.before.bin") (snapshot start)
    IO.FS.writeBinFile (dir/s!"case-{idx}.after.bin") (snapshot done.state)
    IO.FS.writeBinFile (dir/s!"case-{idx}.expected.bin") (snapshot want)
    check s!"{f.label}: snapshot, status {done.state.getReg .x10 |>.toNat}, offset {done.state.getReg .x11 |>.toNat}"
      (snapshot done.state == snapshot want)
    measurements := measurements ++ s!"{idx} {f.label} {done.steps} bound={budget}\n"
  IO.FS.writeFile (dir/"measurements.txt") measurements
  IO.println s!"PASS {kind}: {fs.size} Spec/instructions/full snapshot/footprint cases"

def main (args : List String) : IO Unit := do
  match args with
  | [kind,dir] => run kind dir
  | _ => throw (IO.userError "usage: quic-wire-probe kind directory")

end Libp2pAsm.Tests.QuicWire
