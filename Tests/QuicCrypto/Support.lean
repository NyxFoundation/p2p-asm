import Libp2pAsm.Asm.Crypto.Quic.Kdf
import Libp2pAsm.Asm.Crypto.Quic.Packet
import Libp2pAsm.Asm.Crypto.Quic.Retry
import Libp2pAsm.Spec.Crypto.Quic.Packet
import Tests.HashCrypto.Support

namespace Libp2pAsm.Tests.QuicCrypto
open Rv64
open HashCrypto (Case replaced)
open AsmCrypto (snapshot check readLE wordBytes)

def body (kind : String) : Except String SAsm.Stmt := match kind with
  | "initial" => Asm.Crypto.Quic.Kdf.derive .initial
  | "keys" => Asm.Crypto.Quic.Kdf.derive .keys
  | "update" => Asm.Crypto.Quic.Kdf.derive .update
  | "nonce" => .ok Asm.Crypto.Quic.nonce
  | "number" => .ok Asm.Crypto.Quic.reconstruct
  | "seal" => Asm.Crypto.Quic.Packet.protect
  | "open" => Asm.Crypto.Quic.Packet.unprotect
  | "retry" => Asm.Crypto.Quic.Retry.generate
  | "retrycheck" => Asm.Crypto.Quic.Retry.check
  | _ => .error "unknown QUIC operation"

def reference (kind : String) (c : Case) : Except String (Array UInt8) :=
  let r : Except Spec.Crypto.Quic.Error (Array UInt8) := do
    let pn := c.field 3
    let off := c.field 7
    let hlen := c.field 8
    let d := ((c.start.memory.regions[4]?).getD (⟨0,#[],false⟩ : Region)).bytes
    let limit := (readLE d (8+(if kind == "seal" || kind == "open" then 72 else 64))).toNat
    match kind with
    | "initial" => return (← Spec.Crypto.Quic.initial c.a.toList).toArray
    | "keys" => return (← Spec.Crypto.Quic.packetKeys c.a.toList).toArray
    | "update" => return (← Spec.Crypto.Quic.update c.a.toList).toArray
    | "nonce" => Spec.Crypto.Quic.nonce c.a pn
    | "number" => return wordBytes [BitVec.ofNat 64 (← Spec.Crypto.Quic.reconstruct pn off hlen)]
    | "seal" => Spec.Crypto.Quic.protect c.a c.b off hlen pn limit
    | "open" =>
      let p ← Spec.Crypto.Quic.unprotect c.a c.b off pn limit
      return wordBytes [BitVec.ofNat 64 p.number, BitVec.ofNat 64 p.headerLength] ++ p.packet
    | "retry" => Spec.Crypto.Quic.retryTag c.a c.b
    | "retrycheck" => Spec.Crypto.Quic.retryCheck c.a c.b *> pure #[]
    | _ => throw .crypto
  r.mapError reprStr

def expected (c : Case) (result : Array UInt8) : State :=
  let regions := c.start.memory.regions.mapIdx fun i r =>
    let bytes := if i == 2 && c.field 0 == 0 then replaced r.bytes (8+c.field 5) result
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
    (!write && ((inside 0x500008 (c.field 9)) || inside 0x500108 512 ||
      ((c.field 1 > 0 || c.field 0 == 0) && inside (0x100008+c.field 5) c.a.size) ||
      ((c.field 1 > 0 || c.field 0 == 3) && inside (0x200008+c.field 5) c.b.size))) ||
    ((c.field 1 > 0 || c.field 0 == 0) && inside (0x300008+c.field 5) (c.field 6)) ||
    inside 0x400008 (c.field 1) || inside (0x600400-c.field 2) (c.field 2)

def tracePair (p : Program) (c : Case) : Nat → State → State → Except String State
  | 0,a,b => if a.pc == 0x80000 && b.pc == 0x80000 then .ok b else .error "trace fuel"
  | n+1,a,b => do
    let ia ← (p.fetch a.pc).mapError reprStr
    let ib ← (p.fetch b.pc).mapError reprStr
    let ea := AsmCrypto.event ia a
    unless ea == AsmCrypto.event ib b && permitted c ea do throw s!"trace/footprint {repr ea}"
    tracePair p c n (← (execInstr ia a).mapError reprStr) (← (execInstr ib b).mapError reprStr)

end Libp2pAsm.Tests.QuicCrypto
