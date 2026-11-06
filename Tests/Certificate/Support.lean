import Libp2pAsm.Spec.Identity.X509.Certificate
import Libp2pAsm.Asm.Identity.X509.Certificate
import Tests.HashCrypto.Support

namespace Libp2pAsm.Tests.Certificate
open Rv64
open HashCrypto (Case replaced)
open AsmCrypto (readLE wordBytes)

structure Outcome where
  status : Nat
  output : Array UInt8 := #[]
  wipe : Nat := 0
  depth : Nat := 0

def arg (c : Case) (i : Nat) : Nat :=
  match c.start.memory.regions[4]? with
  | none => panic! "certificate fixture has no descriptor region"
  | some region => (readLE region.bytes (8+8*i)).toNat

def reg (c : Case) (r : Reg) : Nat := (c.start.getReg r).toNat

def span (p n : Nat) : Bool := n == 0 || p+n ≤ 2^64

def preflight (c : Case) : Nat :=
  let d := reg c .x10
  let n := arg c 1
  let work := 512+4*n
  let sp := reg c .x2
  let spans := [(d,64),(sp-144,144),(arg c 0,n),(arg c 2,168),(arg c 4,work)]
  if d % 8 != 0 || !span d 64 then 4
  else if n ≥ 2^61 then 2
  else if arg c 6 == 0 || arg c 6 < n || arg c 7 == 0 then 12
  else if arg c 3 < 168 || arg c 5 < work then 5
  else if arg c 4 % 8 != 0 || sp < 144 || sp % 16 != 0 then 4
  else if spans.any (fun (p,n) => !span p n) then 4
  else if spans.zipIdx.any (fun ((a,n),i) => (spans.drop (i+1)).any fun (b,m) =>
    n != 0 && m != 0 && a < b+m && b < a+n) then 4
  else 0

def serialize (c : Spec.Identity.X509.Certificate) : Array UInt8 :=
  wordBytes (([c.tbs.offset,c.tbs.length,c.spki.offset,c.spki.length,c.key.kind,
    c.key.data.offset,c.key.data.length,c.key.modulus.offset,c.key.modulus.length,
    c.key.exponent.offset,c.key.exponent.length,c.signatureKind,
    c.signature.offset,c.signature.length,
    (BitVec.ofInt 64 c.notBefore).toNat,(BitVec.ofInt 64 c.notAfter).toNat,
    c.hostKey.offset,c.hostKey.length,c.hostSignature.offset,c.hostSignature.length,
    c.usage]).map (BitVec.ofNat 64))

def reference (c : Case) : Except String Outcome := do
  let early := preflight c
  if early != 0 then return {status := early}
  unless c.a.size == arg c 1 do throw "fixture length is not represented"
  let base : Outcome := {status := 0, wipe := 512+4*c.a.size, depth := 144}
  let parsed := Spec.Identity.X509.certificate c.a.toList
  if c.field 3 == 1 then
    unless parsed.isOk && arg c 7 == 1 do throw "invalid one-operation exhaustion fixture"
    return {base with status := 12}
  match parsed with
  | .error e => return {base with status := e.code}
  | .ok decoded => return {base with output := serialize decoded}

def expected (c : Case) (o : Outcome) : State :=
  let regions := c.start.memory.regions.mapIdx fun i r =>
    let bytes := if i == 2 && o.status == 0 then replaced r.bytes (8+c.field 4) o.output
      else if i == 3 && o.wipe > 0 then replaced r.bytes 8 (Array.replicate o.wipe 0)
      else if i == 5 && o.depth > 0 then
        replaced r.bytes (416-o.depth) (Array.replicate o.depth 0)
      else r.bytes
    {r with bytes}
  let s := Asm.Crypto.Sha2.cleared.foldl (fun s r => s.setReg r 0) c.start
  {s.setReg .x10 (BitVec.ofNat 64 o.status) with pc := 0x80000, memory := ⟨regions⟩}

def permitted (c : Case) (o : Outcome) (e : AsmCrypto.Event) : Bool :=
  match e.access with
  | none => true
  | some (write,width,address) =>
    let inside := fun p n => p ≤ address.toNat && address.toNat+width ≤ p+n
    (!write && width == 8 && reg c .x10 % 8 == 0 &&
      span (reg c .x10) 64 && inside (reg c .x10) 64) ||
    (o.depth != 0 && ((!write && width == 1 && inside (arg c 0) c.a.size) ||
      (write && o.status == 0 && width == 1 && inside (arg c 2) 168) ||
      inside (arg c 4) o.wipe || inside (reg c .x2-o.depth) o.depth))

/-- Fused diagnostic trace checking avoids retaining millions of event records.
It still fetches and checks every actual instruction and memory access. -/
def checkedRun (p : Program) (c : Case) (o : Outcome) :
    Nat → State → Array UInt8 → Except String (Nat × State × Array UInt8)
  | 0, _, _ => .error "certificate probe instruction budget"
  | n+1, s, coverage => do
    if s.pc == 0x80000 then return (n+1,s,coverage)
    let i ← (p.fetch s.pc).mapError reprStr
    unless permitted c o (AsmCrypto.event i s) do
      throw s!"certificate footprint {repr (AsmCrypto.event i s)}"
    let coverage := coverage.set! ((s.pc.toNat-p.base.toNat)/4) 1
    checkedRun p c o n (← (execInstr i s).mapError reprStr) coverage

end Libp2pAsm.Tests.Certificate
