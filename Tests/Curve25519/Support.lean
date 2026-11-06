import Libp2pAsm.Asm.Crypto.Curve25519.X25519
import Libp2pAsm.Asm.Crypto.Curve25519.Ed25519
import Libp2pAsm.Asm.Crypto.Curve25519.Verify
import Libp2pAsm.Spec.Crypto.Curve25519.X25519
import Libp2pAsm.Spec.Crypto.Curve25519.Ed25519
import Tests.HashCrypto.Support

namespace Libp2pAsm.Tests.Curve25519
open Rv64
open HashCrypto (Case replaced loadCase)
open AsmCrypto (snapshot check)

def body (kind : String) : Except String SAsm.Stmt := match kind with
  | "edpublic" => Asm.Crypto.Curve25519.Ed25519.publicKey
  | "edsign" => Asm.Crypto.Curve25519.Ed25519.sign
  | "edverify" => Asm.Crypto.Curve25519.Verify.verify
  | "xpublic" => Asm.Crypto.Curve25519.X25519.publicKey
  | "xshared" => Asm.Crypto.Curve25519.X25519.sharedSecret
  | "xraw" => Asm.Crypto.Curve25519.X25519.raw
  | _ => .error "unknown curve algorithm"

def reference (kind : String) (c : Case) : Except String (Array UInt8) := do
  let a := c.a.toList
  let b := c.b.toList
  let result := match kind with
    | "edpublic" => Spec.Crypto.Curve25519.Ed25519.publicKey a
    | "edsign" => Spec.Crypto.Curve25519.Ed25519.sign a b
    | "edverify" =>
      let region := (c.start.memory.regions[2]?).getD (⟨0,#[],false⟩ : Region)
      let signature := (region.bytes.extract (8+c.field 5) (8+c.field 5+c.field 6)).toList
      (Spec.Crypto.Curve25519.Ed25519.verify a b signature).map (fun _ => [])
    | "xpublic" => Spec.Crypto.Curve25519.X25519.publicKey a
    | "xshared" => Spec.Crypto.Curve25519.X25519.sharedSecret a b
    | _ => Spec.Crypto.Curve25519.X25519.raw a b
  return (← result.mapError reprStr).toArray

def expected (c : Case) (result : Array UInt8) : State :=
  let regions := c.start.memory.regions.mapIdx fun i r =>
    let bytes := if i == 2 && c.field 0 == 0 then replaced r.bytes (8+c.field 5) result
      else if i == 3 && c.field 1 > 0 then replaced r.bytes 8 (Array.replicate (c.field 1) 0)
      else if i == 5 && c.field 2 > 0 then
        replaced r.bytes (1024-c.field 2) (Array.replicate (c.field 2) 0)
      else r.bytes
    {r with bytes := bytes}
  let s := Asm.Crypto.Sha2.cleared.foldl (fun s r => s.setReg r 0) c.start
  {s.setReg .x10 (BitVec.ofNat 64 (c.field 0)) with pc := 0x80000, memory := ⟨regions⟩}

/-- Only the secret changes: peer, lengths, all addresses and capabilities stay equal. -/
def changed (c : Case) : Case :=
  let a := if c.field 3 == 1 then c.a else c.a.map (· ^^^ 0xff)
  let regions := c.start.memory.regions.mapIdx fun i r =>
    if i == 0 then {r with bytes := replaced r.bytes (8+c.field 5) a} else r
  {c with a := a, start := {c.start with memory := ⟨regions⟩}}

def permitted (c : Case) (e : AsmCrypto.Event) : Bool := match e.access with
  | none => true
  | some (write,width,addr) =>
    let inside := fun base size => base ≤ addr.toNat && addr.toNat+width ≤ base+size
    (!write && ((c.field 0 != 9 && inside (0x100008+c.field 5) c.a.size) ||
      inside (0x200008+c.field 5) c.b.size)) ||
    ((!write || c.field 3 != 1) && inside (0x300008+c.field 5) (c.field 7)) || inside 0x400008 (c.field 1) ||
    inside (0x600400-c.field 2) (c.field 2)

def tracePair (p : Program) (c : Case) : Nat → State → State → Except String State
  | 0,a,b => if a.pc == 0x80000 && b.pc == 0x80000 then .ok b else .error "trace fuel"
  | n+1,a,b => do
    let ia ← (p.fetch a.pc).mapError reprStr
    let ib ← (p.fetch b.pc).mapError reprStr
    let ea := AsmCrypto.event ia a
    unless ea == AsmCrypto.event ib b && permitted c ea do throw s!"trace/footprint {repr ea}"
    tracePair p c n (← (execInstr ia a).mapError reprStr) (← (execInstr ib b).mapError reprStr)

end Libp2pAsm.Tests.Curve25519
