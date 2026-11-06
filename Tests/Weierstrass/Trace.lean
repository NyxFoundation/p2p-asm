import Tests.Weierstrass.Reference

namespace Libp2pAsm.Tests.Weierstrass
open Rv64

def apiKind (kind : String) : Bool :=
  kind == "public" || kind == "ecdh" || kind == "parseder" || kind.startsWith "sign" || kind.startsWith "verify"

/-- Guard reads are forbidden as well as writes; public rejections must not read
secret material. Test fixture ranges are independent of the generated code. -/
structure AccessContract where
  reads : Array (Nat × Nat)
  writes : Array (Nat × Nat)

def accessContract (kind : String) (f : Fixture) : AccessContract := Id.run do
  let outputSize := if apiKind kind && ([1,4,5,9].contains f.status) then 0 else f.expected.size
  let writes := #[(base f.outputRegion+f.outputOffset,outputSize),
    (base f.wipeRegion+8,f.wipeLength),(stackTop-f.stackDepth,f.stackDepth)]
  if !apiKind kind then return ⟨#[(base 0+8,(f.regions[0]!).size-16),
    (base 1+8,(f.regions[1]!).size-16)],writes⟩
  let mut reads := #[(base 1+8,104)]
  if (kind == "public" || kind == "ecdh" || kind.startsWith "sign") &&
      !([1,4,5,9].contains f.status) then reads := reads.push (metadata f 0,metadata f 8)
  if kind == "ecdh" || kind.startsWith "verify" then reads := reads.push (metadata f 16,metadata f 24)
  if kind.startsWith "sign" || kind.startsWith "verify" then reads := reads.push (metadata f 32,metadata f 40)
  if kind.startsWith "verify" || kind == "parseder" then reads := reads.push (metadata f 48,metadata f 56)
  if kind.startsWith "sign" then reads := reads.push (metadata f 96,512)
  return ⟨reads,writes⟩

def footprint (contract : AccessContract) (event : AsmCrypto.Event) : Bool :=
  match event.access with
  | none => true
  | some (write,width,address) =>
    let inside := fun (start,size) => start ≤ address.toNat && address.toNat+width ≤ start+size
    contract.writes.any inside || (!write && contract.reads.any inside)

/-- Exact lockstep control/access comparison, constant host memory. The optional
second state uses the same program and public buffer layout. Instruction values
are executed through the unchanged RV64 model; neither execution is replaced by
a crypto oracle. This finite diagnostic is not a universal constant-time proof. -/
def checkedLoop (p : Program) (contract : AccessContract) :
    Nat → State → Option State → Nat → Except String Completed
  | 0, _, _, _ => .error "fuel exhausted"
  | fuel+1, state, peer, count => do
    if state.pc == 0x80000 then
      unless peer.all (fun q => q.pc == 0x80000) do throw "trace termination differs"
      return ⟨state,count⟩
    let instr ← (p.fetch state.pc).mapError (fun e => s!"fetch {repr e}")
    let event := AsmCrypto.event instr state
    unless footprint contract event do throw s!"guard access at step {count} pc {state.pc.toNat}"
    let peer ← peer.mapM fun other => do
      let nextInstr ← (p.fetch other.pc).mapError (fun _ => "paired fetch")
      unless AsmCrypto.event nextInstr other == event do throw s!"trace differs at step {count}"
      (execInstr nextInstr other).mapError (fun _ => "paired execution")
    let next ← (execInstr instr state).mapError (fun e => s!"execution {repr e} at {count}")
    checkedLoop p contract fuel next peer (count+1)

end Libp2pAsm.Tests.Weierstrass
