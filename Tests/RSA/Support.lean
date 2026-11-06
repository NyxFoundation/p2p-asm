import Lean
import Libp2pAsm.Asm.Crypto.RSA.Api
import Libp2pAsm.Spec.Crypto.RSA.EMSA
import Libp2pAsm.Codegen.Assembly
import Libp2pAsm.Rv64.Execution

namespace Libp2pAsm.Tests.RSA
open Rv64

structure Fixture where
  label : String
  regions : Array (Array Nat)
  args : Array Nat
  status : Nat
  wipeLength : Nat
  stackDepth : Nat
  stack : Nat := 0x251000
  workOffset : Nat := 8
  checkSpec : Bool := true
  n : Array Nat := #[]
  e : Array Nat := #[]
  signature : Array Nat := #[]
  digest : Array Nat := #[]
  deriving Lean.FromJson, Inhabited

def base (i : Nat) : Nat := 0x200000+0x10000*i

def wordBytes (xs : List Nat) : Array UInt8 :=
  (xs.flatMap fun x => (List.range 8).map fun i => (x / 2^(8*i) % 256).toUInt8).toArray

def initial (f : Fixture) : State := Id.run do
  let rs := f.regions.mapIdx fun i xs =>
    (⟨BitVec.ofNat 64 (base i), xs.map Nat.toUInt8, i == 3 || i == 5⟩ : Region)
  let mut s : State := {
    pc := 0x10000
    memory := ⟨rs⟩
    regs := Vector.ofFn fun i => BitVec.ofNat 64 (0x8192a3b4c5d6e700+i.val) }
  s := ((s.setReg .x1 0x80000).setReg .x2 (BitVec.ofNat 64 f.stack)).setReg .x3 0x280000
  for (r,n) in ([Reg.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17].zip f.args.toList) do
    s := s.setReg r (BitVec.ofNat 64 n)
  return s

def snapshot (s : State) : ByteArray :=
  let rs := wordBytes ((List.finRange 32).map fun i => if i.val == 0 then 0 else s.regs[i].toNat)
  ⟨s.memory.regions.foldl (fun xs r => xs ++ r.bytes) rs⟩

def replace (xs : Array UInt8) (off size : Nat) : Array UInt8 :=
  xs.extract 0 off ++ Array.replicate size 0 ++ xs.extract (off+size) xs.size

def expected (f : Fixture) (s : State) : State :=
  let rs := s.memory.regions.mapIdx fun i r =>
    {r with bytes := if i == 3 then replace r.bytes f.workOffset f.wipeLength else
      if i == 5 then replace r.bytes (4096-f.stackDepth) f.stackDepth else r.bytes}
  let s := Asm.Crypto.Sha2.cleared.foldl (fun s r => s.setReg r 0) s
  {s.setReg .x10 (BitVec.ofNat 64 f.status) with pc := 0x80000, memory := ⟨rs⟩}

def inside (addr width start size : Nat) : Bool :=
  start ≤ addr && addr+width ≤ start+size

/-- Guards cannot be read or written. Preflight failures cannot write at all.
Mappings are checked by the ISA memory model as well. -/
def accessAllowed (f : Fixture) (s : State) (i : Instr) : Bool :=
  let acc := match i with
    | .LD _ b o => some (false, 8, s.getReg b + o.signExtend 64)
    | .LBU _ b o => some (false, 1, s.getReg b + o.signExtend 64)
    | .SD b _ o => some (true, 8, s.getReg b + o.signExtend 64)
    | .SB b _ o => some (true, 1, s.getReg b + o.signExtend 64)
    | _ => none
  match acc with
  | none => true
  | some (write, width, addr) =>
    let a := addr.toNat
    let work := inside a width (base 3+f.workOffset) f.wipeLength
    let stack := inside a width (0x251000-f.stackDepth) f.stackDepth
    if f.stackDepth == 0 then !write && inside a width (base 2+8) 128 else
    if write then work || stack else
      work || stack || (List.range 5).any (fun j => j != 3 &&
        inside a width (base j+8) (f.regions[j]!.size-16))

def checkedLoop (p : Program) (f : Fixture) : Nat → State → Nat → Except String Completed
  | 0, _, _ => .error "instruction bound exhausted"
  | fuel+1, s, steps => do
    if s.pc == 0x80000 then return ⟨s,steps⟩
    let i ← (p.fetch s.pc).mapError (fun e => s!"fetch: {repr e}")
    unless accessAllowed f s i do throw s!"footprint at {s.pc.toNat}: {repr i}"
    let next ← (execInstr i s).mapError (fun e => s!"execute: {repr e}")
    checkedLoop p f fuel next (steps+1)

def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

end Libp2pAsm.Tests.RSA
