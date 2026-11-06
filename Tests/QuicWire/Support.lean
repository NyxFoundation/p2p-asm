import Lean
import Libp2pAsm.Asm.Quic.Wire.Packet
import Libp2pAsm.Spec.Quic.Wire.Packet
import Libp2pAsm.Spec.Quic.Wire.Frame
import Libp2pAsm.Asm.Quic.Wire.Frame
import Libp2pAsm.Spec.Quic.Wire.Transport
import Libp2pAsm.Asm.Quic.Wire.Transport
import Libp2pAsm.Spec.Quic.Wire.Descriptors
import Libp2pAsm.Asm.Quic.Wire.PacketEncode
import Libp2pAsm.Asm.Quic.Wire.FrameEncode
import Libp2pAsm.Asm.Quic.Wire.TransportEncode
import Libp2pAsm.Asm.Quic.Wire.Permission
import Libp2pAsm.Asm.Quic.Wire.Batch
import Libp2pAsm.Spec.Quic.Wire.Batch
import Libp2pAsm.Asm.Quic.Wire.Resources
import Libp2pAsm.Codegen.Assembly
import Libp2pAsm.Rv64.Execution

namespace Libp2pAsm.Tests.QuicWire
open Rv64

structure Fixture where
  label : String
  regions : Array (Array Nat)
  args : Array Nat
  status : Nat
  errorOffset : Nat := 0
  consumed : Nat := 0
  output : Array Nat := #[]
  wipeLength : Nat := 128
  stackDepth : Nat := 256
  checkSpec : Bool := true
  inputOffset : Nat := 9
  outputOffset : Nat := 11
  workOffset : Nat := 8
  stack : Nat := 0x251000
  deriving Lean.FromJson, Inhabited

def base (i : Nat) : Nat := 0x200000+0x10000*i

def initial (f : Fixture) : State := Id.run do
  let rs := f.regions.mapIdx fun i xs =>
    (⟨BitVec.ofNat 64 (base i), xs.map Nat.toUInt8, i == 1 || i == 2 || i == 5⟩ : Region)
  let mut s : State := {
    pc := 0x10000
    memory := ⟨rs⟩
    regs := Vector.ofFn fun i => BitVec.ofNat 64 (0x8192a3b4c5d6e700+i.val)}
  s := ((s.setReg .x1 0x80000).setReg .x2 (BitVec.ofNat 64 f.stack)).setReg .x3 0x280000
  for (r,n) in ([Reg.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17].zip f.args.toList) do
    s := s.setReg r (BitVec.ofNat 64 n)
  return s

def snapshot (s : State) : ByteArray :=
  let rs := Spec.Quic.Wire.packWords ((List.finRange 32).map fun i =>
    if i.val == 0 then 0 else s.regs[i].toNat)
  ⟨s.memory.regions.foldl (fun xs r => xs ++ r.bytes) rs.toArray⟩

def replace (xs : Array UInt8) (off : Nat) (bs : Array UInt8) : Array UInt8 :=
  xs.extract 0 off ++ bs ++ xs.extract (off+bs.size) xs.size

def expected (f : Fixture) (s : State) : State :=
  let rs := s.memory.regions.mapIdx fun i r =>
    {r with bytes := if i == 1 then replace r.bytes f.outputOffset (f.output.map Nat.toUInt8) else
      if i == 2 then replace r.bytes f.workOffset (Array.replicate f.wipeLength 0) else
      if i == 5 then replace r.bytes (4096-f.stackDepth) (Array.replicate f.stackDepth 0) else r.bytes}
  let s := Asm.Crypto.Sha2.cleared.foldl (fun s r => s.setReg r 0) s
  let s := ((s.setReg .x10 (BitVec.ofNat 64 f.status)).setReg .x11
    (BitVec.ofNat 64 f.errorOffset)).setReg .x12 (BitVec.ofNat 64 f.consumed)
  {s with pc := 0x80000, memory := ⟨rs⟩}

def inside (a width start size : Nat) : Bool := start ≤ a && a+width ≤ start+size

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
    let work := inside a width (base 2+f.workOffset) f.wipeLength
    let stack := inside a width (0x251000-f.stackDepth) f.stackDepth
    if f.stackDepth == 0 then false else
    if write then work || stack || inside a width (base 1+f.outputOffset) f.output.size else
      work || stack || inside a width f.args[0]! f.args[1]!

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

end Libp2pAsm.Tests.QuicWire
