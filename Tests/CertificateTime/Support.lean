import Libp2pAsm.Spec.Identity.Time
import Libp2pAsm.Asm.Identity.Time
import Tests.HashCrypto.Support

namespace Libp2pAsm.Tests.CertificateTime.Native
open Rv64 HashCrypto

structure Outcome where
  status : Nat
  value : Nat := 0
  bytes : Array UInt8 := #[]

def word (c : Case) (r : Reg) : Nat := (c.start.getReg r).toNat

def span (ptr size : Nat) : Bool := ptr+size ≤ 2^64

private def decoded (c : Case) : Except String Outcome := do
  let tag := word c .x10
  if tag != 23 && tag != 24 then return { status := 6 }
  if word c .x12 != (if tag == 23 then 13 else 15) then return { status := 1 }
  if !span (word c .x11) (word c .x12) then return { status := 4 }
  unless c.a.size == word c .x12 do throw "invalid time input fixture"
  match Spec.Identity.Time.decode tag c.a.toList with
  | .error e => return { status := e.code }
  | .ok n => return { status := 0, value := (BitVec.ofInt 64 n).toNat }

private def encoded (c : Case) : Outcome :=
  match Spec.Identity.Time.encode (c.start.getReg .x10).toInt with
  | .error e => { status := e.code }
  | .ok bytes =>
    if word c .x12 < bytes.length then { status := 5 }
    else if !span (word c .x11) bytes.length then { status := 4 }
    else { status := 0, value := bytes.length, bytes := bytes.toArray }

def reference (kind : String) (c : Case) : Except String Outcome :=
  if kind == "decode" then decoded c
  else if kind == "encode" then .ok (encoded c)
  else if kind == "validity" then .ok (match Spec.Identity.Time.validity
      (c.start.getReg .x10).toInt (c.start.getReg .x11).toInt (c.start.getReg .x12).toInt with
    | .ok () => { status := 0 } | .error e => { status := e.code })
  else .error "unknown time operation"

def expected (c : Case) (o : Outcome) : State :=
  let regions := c.start.memory.regions.mapIdx fun i r =>
    if i == 2 && !o.bytes.isEmpty then
      { r with bytes := replaced r.bytes (word c .x11-r.base.toNat) o.bytes }
    else r
  let state := Asm.Crypto.Sha2.cleared.foldl (fun s r => s.setReg r 0) c.start
  { state.setReg .x10 (BitVec.ofNat 64 o.status) |>.setReg .x11 (BitVec.ofNat 64 o.value)
    with pc := 0x80000, memory := ⟨regions⟩ }

def permitted (kind : String) (c : Case) (o : Outcome) (e : AsmCrypto.Event) : Bool :=
  match e.access with
  | none => true
  | some (write, width, addr) =>
    let ptr := word c .x11
    let size := if kind == "decode" then c.a.size else o.bytes.size
    let admitted := if kind == "decode" then
      (word c .x10 == 23 || word c .x10 == 24) &&
      word c .x12 == (if word c .x10 == 23 then 13 else 15) &&
      span ptr (word c .x12) else o.status == 0
    admitted && width == 1 && write == (kind == "encode") &&
      ptr ≤ addr.toNat && addr.toNat+width ≤ ptr+size

end Libp2pAsm.Tests.CertificateTime.Native
