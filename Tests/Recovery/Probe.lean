import Tests.Recovery.Support

open Libp2pAsm Libp2pAsm.Rv64 Libp2pAsm.Tests Libp2pAsm.Tests.Recovery

def main (args : List String) : IO Unit := do
  let [kind,directory] := args | throw (IO.userError "usage: recoveryProbe kind directory")
  let dir : System.FilePath := directory
  let c ← HashCrypto.loadCase dir 0
  let input := words (regionPayload c.start 0)
  let state := words (regionPayload c.start 2)
  let abi := Spec.Quic.Recovery.validateAbi (c.start.getReg .x10).toNat
    (c.start.getReg .x2).toNat (words (regionPayload c.start 4))
  let answer := abi *> invoke kind state input
  let expected := expected c answer (match abi with | .ok _ => true | .error _ => false)
  let .ok body := Asm.Quic.Recovery.program kind | throw (IO.userError "program validation")
  let .ok code := body.lower | throw (IO.userError "lower")
  let .ok bytes := encodeProgram code | throw (IO.userError "encode")
  IO.FS.writeFile (dir / "protocol.S") (Codegen.assembly code)
  IO.FS.writeBinFile (dir / "encoded.bin") bytes
  AsmCrypto.check "code/mapping separation" ((Program.mk 0x10000 code).valid c.start.memory)
  let limits := if kind == "init" then
      (⟨input[5]!,input[6]!,input[7]!,input[8]!,input[9]!,input[10]!,input[11]!,input[12]!,input[13]!,input[14]!,input[15]!⟩ : Spec.Quic.Recovery.Config)
    else Spec.Quic.Recovery.configFromWords state
  let bound := min limits.quantum (Spec.Quic.Recovery.quantumBound limits)
  let actual ← match execute ⟨0x10000,code⟩ c.start bound c.start 0 with
    | .ok pair => pure pair
    | .error err => throw (IO.userError err)
  IO.FS.writeBinFile (dir / "case-0" / "after.bin") (AsmCrypto.snapshot actual.1)
  IO.FS.writeBinFile (dir / "case-0" / "expected.bin") (AsmCrypto.snapshot expected)
  IO.FS.writeFile (dir / "case-0" / "steps.txt") s!"{actual.2}\n"
  AsmCrypto.check s!"Spec/full snapshot status={actual.1.getReg .x10} expected={expected.getReg .x10}"
    (AsmCrypto.snapshot actual.1 == AsmCrypto.snapshot expected)
  IO.println s!"PASS {kind}: {actual.2} instructions"
