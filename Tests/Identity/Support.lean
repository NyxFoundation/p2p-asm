import Libp2pAsm.Spec.Identity.PublicKey
import Libp2pAsm.Asm.Identity.PublicKey
import Tests.HashCrypto.Support

namespace Libp2pAsm.Tests.Identity.Native
open Rv64
open HashCrypto (Case replaced)

structure Outcome where
  status : Nat
  fields : List Nat := []
  bytes : Array UInt8 := #[]
  wipe : Nat := 0
  depth : Nat := 0

def word (c : Case) (r : Reg) : Nat := (c.start.getReg r).toNat

def span (ptr size : Nat) : Bool := size == 0 || ptr + size ≤ 2^64

def overlaps (a n b m : Nat) : Bool :=
  n != 0 && m != 0 && a < b+m && b < a+n

def preflight (c : Case) : Nat :=
  let ptr := word c .x10
  let size := word c .x11
  let work := word c .x12
  let bytes := size*8
  let sp := word c .x2
  if size ≥ 2^61 then 2
  else if size == 0 then 7
  else if word c .x13 < bytes then 5
  else if !span ptr size || !span work bytes || work % 8 != 0 ||
      sp < 112 || sp % 16 != 0 || overlaps ptr size work bytes ||
      overlaps ptr size (sp-112) 112 || overlaps work bytes (sp-112) 112 then 4
  else 0

private def publicKey (c : Case) : Except String Outcome := do
  let early := preflight c
  if early != 0 then return { status := early }
  unless word c .x11 == c.a.size do throw "invalid represented input fixture"
  let base : Outcome := { status := 0, wipe := c.a.size*8, depth := 112 }
  match Spec.Identity.PublicKey.decode c.a.toList with
  | .error e => return { base with status := e.code }
  | .ok d => return { base with fields := [d.kind, d.offset, d.length] }

private def varint (c : Case) : Except String Outcome := do
  if !span (word c .x10) (word c .x11) then return { status := 4 }
  unless word c .x11 == c.a.size do throw "invalid represented input fixture"
  match Spec.Codec.ProtobufVarint.decode c.a.toList with
  | .error e => return { status := if e == .truncated then 1 else 2 }
  | .ok d => return { status := 0, fields := [d.value, d.consumed] }

private def peerId (c : Case) : Except String Outcome := do
  let kind := word c .x10
  let size := word c .x12
  if kind != 1 && kind != 2 then return { status := 8 }
  if size != kind + 31 then return { status := 9 }
  if word c .x14 < size + 6 then return { status := 5 }
  if !span (word c .x11) size || !span (word c .x13) (size+6) ||
      overlaps (word c .x11) size (word c .x13) (size+6) then return { status := 4 }
  unless size == c.a.size do throw "invalid represented key fixture"
  let bytes ← (Spec.Identity.PublicKey.peerId kind c.a.toList).mapError reprStr
  return { status := 0, fields := [bytes.length], bytes := bytes.toArray }

def reference (kind : String) (c : Case) : Except String Outcome :=
  match kind with
  | "publickey" => publicKey c
  | "varint" => varint c
  | "peerid" => peerId c
  | _ => .error "unknown identity operation"

def expected (c : Case) (o : Outcome) : State :=
  let regions := c.start.memory.regions.mapIdx fun i r =>
    let bytes := if i == 2 && !o.bytes.isEmpty then replaced r.bytes 8 o.bytes
      else if i == 3 && o.wipe > 0 then replaced r.bytes 8 (Array.replicate o.wipe 0)
      else if i == 5 && o.depth > 0 then
        replaced r.bytes (416-o.depth) (Array.replicate o.depth 0)
      else r.bytes
    { r with bytes }
  let base := Asm.Crypto.Sha2.cleared.foldl (fun s r => s.setReg r 0) c.start
  let outputs : List Reg := [.x11, .x12, .x13]
  let result := (outputs.zip o.fields).foldl
    (fun s (r, n) => s.setReg r (BitVec.ofNat 64 n))
    (base.setReg .x10 (BitVec.ofNat 64 o.status))
  { result with pc := 0x80000, memory := ⟨regions⟩ }

def permitted (kind : String) (c : Case) (o : Outcome) (e : AsmCrypto.Event) : Bool :=
  match e.access with
  | none => true
  | some (write, width, addr) =>
    let inside := fun base size => base ≤ addr.toNat && addr.toNat + width ≤ base + size
    if kind == "varint" then
      o.status != 4 && !write && width == 1 && inside (word c .x10) (min c.a.size 10)
    else if kind == "peerid" then
      o.status == 0 && width == 1 &&
        (if write then inside (word c .x13) o.bytes.size else inside (word c .x11) c.a.size)
    else o.depth != 0 &&
      ((!write && width == 1 && inside (word c .x10) c.a.size) ||
        inside (word c .x12) o.wipe || inside (word c .x2-o.depth) o.depth)

end Libp2pAsm.Tests.Identity.Native
