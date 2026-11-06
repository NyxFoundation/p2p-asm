import Lean
import Libp2pAsm.Asm.Kernel.Common
import Libp2pAsm.Spec.Kernel.Words
import Libp2pAsm.Rv64.Execution
import Libp2pAsm.Codegen.Assembly

namespace Libp2pAsm.Tests.Kernel
open Rv64

structure Fixture where
  label : String
  regions : Array (Array Nat)
  after : Array (Array Nat)
  args : Array Nat
  status : Nat
  first : Nat := 0
  second : Nat := 0
  entered : Bool := true
  stackDepth : Nat := 256
  extraReads : Array (Array Nat) := #[]
  deriving Lean.FromJson, Inhabited

def base (i : Nat) : Nat := 0x200000+0x10000*i

def initial (f : Fixture) : State := Id.run do
  let mut s : State := {
    pc := 0x10000,
    memory := ⟨f.regions.mapIdx (fun i xs =>
      ⟨BitVec.ofNat 64 (base i),xs.map Nat.toUInt8,i != 1 && i != 4⟩)⟩,
    regs := Vector.ofFn fun i => BitVec.ofNat 64 (0x8192a3b4c5d6e700+i.val)}
  s := ((s.setReg .x1 0x80000).setReg .x2 0x251000).setReg .x3 0x280000
  for (r,n) in ([Reg.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17].zip f.args.toList) do
    s := s.setReg r (BitVec.ofNat 64 n)
  return s

def snapshot (s : State) : ByteArray :=
  let rs := Spec.Kernel.pack ((List.finRange 32).map fun i =>
    if i.val == 0 then 0 else s.regs[i].toNat)
  ⟨s.memory.regions.foldl (fun xs r => xs ++ r.bytes) rs.toArray⟩

def expected (f : Fixture) (s : State) : State :=
  let rs := s.memory.regions.mapIdx fun i r => {r with bytes := f.after[i]!.map Nat.toUInt8}
  let s := Asm.Kernel.temps.foldl (fun s r => s.setReg r 0) s
  let s := ((s.setReg .x10 (BitVec.ofNat 64 f.status)).setReg .x11
    (BitVec.ofNat 64 f.first)).setReg .x12 (BitVec.ofNat 64 f.second)
  {s with pc := 0x80000,memory := ⟨rs⟩}

def inside (a width start size : Nat) : Bool := start ≤ a && a+width ≤ start+size

def accessAllowed (f : Fixture) (s : State) (i : Instr) : Bool :=
  let acc := match i with
    | .LD _ b o => some (false,8,s.getReg b+o.signExtend 64)
    | .LBU _ b o => some (false,1,s.getReg b+o.signExtend 64)
    | .SD b _ o => some (true,8,s.getReg b+o.signExtend 64)
    | .SB b _ o => some (true,1,s.getReg b+o.signExtend 64)
    | _ => none
  match acc with
  | none => true
  | some (write,width,addr) =>
    let a := addr.toNat
    inside a width f.args[0]! f.args[1]! || inside a width f.args[4]! f.args[5]! ||
    (f.entered && inside a width (0x251000-f.stackDepth) f.stackDepth) ||
    (!write && (inside a width f.args[2]! f.args[3]! ||
      f.extraReads.any (fun r => inside a width r[0]! r[1]!)))

def checkedLoop (p : Program) (f : Fixture) : Nat → State → Nat → Except String Completed
  | 0,_,_ => .error "instruction bound exhausted"
  | fuel+1,s,n => do
    if s.pc == 0x80000 then return ⟨s,n⟩
    let i ← (p.fetch s.pc).mapError (fun e => s!"fetch: {repr e}")
    unless accessAllowed f s i do throw s!"footprint at {s.pc.toNat}: {repr i}"
    let next ← (execInstr i s).mapError (fun e => s!"execute: {repr e}")
    checkedLoop p f fuel next (n+1)

def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)
end Libp2pAsm.Tests.Kernel
