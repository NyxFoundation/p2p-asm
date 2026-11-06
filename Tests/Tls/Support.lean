import Libp2pAsm.Spec.Tls.Bounds
import Libp2pAsm.Asm.Tls.Encode
import Libp2pAsm.Spec.Tls.Encode
import Libp2pAsm.Asm.Tls.Codec
import Libp2pAsm.Spec.Tls.Codec
import Libp2pAsm.Asm.Tls.Schedule
import Libp2pAsm.Spec.Tls.Schedule
import Tests.HashCrypto.Support

namespace Libp2pAsm.Tests.Tls
open Rv64
open HashCrypto (Case replaced)
open AsmCrypto (snapshot check)

def mode : String → Asm.Tls.Schedule.Mode
  | "handshake" => .handshake | "application" => .application
  | "finished" => .finished | "messageHash" => .messageHash | _ => .hash

def body (kind : String) : Except String SAsm.Stmt :=
  if kind == "boundary" then .ok Asm.Tls.Codec.admitQuic
  else if kind == "decode" then Asm.Tls.Codec.decode
  else if kind == "encode" then Asm.Tls.Encode.encode
  else if kind == "vector" then .ok Asm.Tls.Encode.vector else Asm.Tls.Schedule.derive (mode kind)

def desc (c : Case) (i : Nat) : Nat :=
  (AsmCrypto.readLE ((c.start.memory.regions[4]?).getD (⟨0,#[],false⟩ : Region)).bytes (8+8*i)).toNat

def verdict (kind : String) (c : Case) : Except Spec.Tls.Error (Array UInt8) :=
  if kind == "boundary" then Spec.Tls.admitQuic (c.a[0]! != 0) c.a[1]!.toNat *> pure #[]
  else if kind == "decode" then
    (Spec.Tls.decode c.a (desc c 6) (c.field 8 == 1)).map
      (fun v => AsmCrypto.wordBytes (v.words.map (BitVec.ofNat 64)))
  else if kind == "encode" then Spec.Tls.encode (desc c 2) c.a (desc c 7) (c.field 8 == 1)
  else if kind == "vector" then do
    let result ← Spec.Tls.vector (desc c 2) (desc c 3) c.a
    if c.a.size > desc c 6 then throw .limit
    return result
  else match kind with
    | "handshake" => (Spec.Tls.Schedule.handshake c.a c.b).map Spec.Tls.Schedule.Handshake.bytes
    | "application" => Spec.Tls.Schedule.application c.a c.b
    | "finished" => Spec.Tls.Schedule.finished c.a c.b
    | "messageHash" => Spec.Tls.Schedule.messageHash c.a c.a.size
    | _ => Spec.Tls.Schedule.hash c.a c.a.size

def reference (kind : String) (c : Case) : Except String (Array UInt8) :=
  (verdict kind c).mapError reprStr

def expected (c : Case) (answer : Array UInt8) : State :=
  let regions := c.start.memory.regions.mapIdx fun i r =>
    let bytes := if i == 2 && c.field 0 == 0 then replaced r.bytes (8+c.field 7) answer
      else if i == 3 && c.field 1 > 0 then replaced r.bytes 8 (Array.replicate (c.field 1) 0)
      else if i == 5 && c.field 2 > 0 then replaced r.bytes (1024-c.field 2) (Array.replicate (c.field 2) 0)
      else r.bytes
    {r with bytes := bytes}
  let s := Asm.Crypto.Sha2.cleared.foldl (fun s r => s.setReg r 0) c.start
  {s.setReg .x10 (BitVec.ofNat 64 (c.field 0)) with pc := 0x80000, memory := ⟨regions⟩}

def permitted (c : Case) (e : AsmCrypto.Event) : Bool := match e.access with
  | none => true
  | some (write,width,addr) =>
    let inside := fun base size => base ≤ addr.toNat && addr.toNat+width ≤ base+size
    (!write && (inside 0x500008 (c.field 9) || inside (0x100008+c.field 5) (c.field 3))) ||
    ((c.field 1 > 0 || c.field 0 == 0) && ((!write && (inside 0x500108 512 ||
      inside (0x100008+c.field 5) c.a.size || inside (0x200008+c.field 5) c.b.size)) ||
      (c.field 0 == 0 && inside (0x300008+c.field 7) (c.field 6)) ||
      inside 0x400008 (c.field 1) || inside (0x600400-c.field 2) (c.field 2)))

/-- Every executed load/store checked, including validation-only failures. -/
def execute (p : Program) (c : Case) : Nat → State → Nat → Except String (State × Nat)
  | 0,_,_ => .error "fuel exhausted"
  | fuel+1,s,n => do
    if s.pc == 0x80000 then return (s,n)
    let i ← (p.fetch s.pc).mapError reprStr
    unless permitted c (AsmCrypto.event i s) do throw s!"footprint {repr (AsmCrypto.event i s)}"
    execute p c fuel (← (execInstr i s).mapError reprStr) (n+1)

def budget (kind : String) (c : Case) : Nat :=
  if kind == "decode" then Spec.Tls.Bounds.decodeSteps c.a.size
  else if kind == "encode" then Spec.Tls.Bounds.encodeSteps c.a.size
  else if kind == "vector" then Spec.Tls.Bounds.vectorSteps c.a.size
  else Spec.Tls.Bounds.transcriptSteps c.a.size

/-- Exact paired branch/access diagnostics, not a universal CT theorem. -/
def tracePair (p : Program) (c : Case) : Nat → State → State → Except String State
  | 0,a,b => if a.pc == 0x80000 && b.pc == 0x80000 then .ok b else .error "trace fuel"
  | fuel+1,a,b => do
    let ia ← (p.fetch a.pc).mapError reprStr
    let ib ← (p.fetch b.pc).mapError reprStr
    let ea := AsmCrypto.event ia a
    unless ea == AsmCrypto.event ib b && permitted c ea do throw "trace/footprint mismatch"
    tracePair p c fuel (← (execInstr ia a).mapError reprStr) (← (execInstr ib b).mapError reprStr)

end Libp2pAsm.Tests.Tls
