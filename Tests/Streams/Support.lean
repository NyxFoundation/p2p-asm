import Lean
import Libp2pAsm.Codegen.Assembly
import Libp2pAsm.Rv64.Execution

namespace Libp2pAsm.Tests.Streams
open Rv64

structure Fixture where
  label : String
  regions : Array (Array Nat)
  expectedRegions : Array (Array Nat)
  args : Array Nat
  outputs : Array Nat
  reads : Array (Array Nat)
  writes : Array (Array Nat)
  budget : Nat := 1000000
  stackUsed : Bool := true
  deriving Lean.FromJson, Inhabited

def base (i : Nat) : Nat := 0x200000 + 0x10000*i

def words (xs : List Nat) : Array UInt8 :=
  (xs.flatMap fun x => (List.range 8).map fun i => (x / 2^(8*i) % 256).toUInt8).toArray

def initial (f : Fixture) : State := Id.run do
  let rs := f.regions.mapIdx fun i xs =>
    (⟨BitVec.ofNat 64 (base i), xs.map Nat.toUInt8, i != 3⟩ : Region)
  let mut s : State := {
    pc := 0x10000
    memory := ⟨rs⟩
    regs := Vector.ofFn fun i => BitVec.ofNat 64 (0x8192a3b4c5d6e700+i.val)}
  s := ((s.setReg .x1 0x80000).setReg .x2 0x251000).setReg .x3 0x280000
  for (r,n) in ([Reg.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17].zip f.args.toList) do
    s := s.setReg r (BitVec.ofNat 64 n)
  return s

def snapshot (s : State) : ByteArray :=
  ⟨s.memory.regions.foldl (fun xs r => xs ++ r.bytes)
    (words ((List.finRange 32).map fun i => if i.val == 0 then 0 else s.regs[i].toNat))⟩

def expected (f : Fixture) (s : State) : State := Id.run do
  let mut s := s
  for r in [Reg.x5,.x6,.x7,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x28,.x29,.x30,.x31] do
    s := s.setReg r 0
  for (r,n) in ([Reg.x10,.x11,.x12,.x13,.x14].zip f.outputs.toList) do
    s := s.setReg r (BitVec.ofNat 64 n)
  let rs := s.memory.regions.mapIdx fun i r => {r with bytes := f.expectedRegions[i]!.map Nat.toUInt8}
  return {s with pc := 0x80000, memory := ⟨rs⟩}

def access (s : State) : Instr → Option (Bool × Nat × Nat)
  | .LD _ b o => some (false, 8, (s.getReg b + o.signExtend 64).toNat)
  | .LBU _ b o => some (false, 1, (s.getReg b + o.signExtend 64).toNat)
  | .SD b _ o => some (true, 8, (s.getReg b + o.signExtend 64).toNat)
  | .SB b _ o => some (true, 1, (s.getReg b + o.signExtend 64).toNat)
  | _ => none

def allowed (ranges : Array (Array Nat)) (a w : Nat) : Bool :=
  ranges.any fun r => r.size == 2 && r[0]! ≤ a && a+w ≤ r[0]!+r[1]!

def checkedLoop (p : Program) (f : Fixture) : Nat → State → Nat → Array UInt8 → Except String (Completed × ByteArray)
  | 0, _, _, _ => .error "instruction bound exhausted"
  | fuel+1, s, steps, trace => do
    if s.pc == 0x80000 then return (⟨s,steps⟩, ⟨trace⟩)
    let i ← (p.fetch s.pc).mapError (fun e => s!"fetch: {repr e}")
    let trace ← match access s i with
      | none => pure trace
      | some (write,w,a) => do
        unless allowed (if write then f.writes else f.reads) a w do
          throw s!"footprint at {s.pc.toNat}: {repr i}, address={a}"
        pure (trace ++ words [s.pc.toNat, if write then 1 else 0, a, w])
    let next ← (execInstr i s).mapError (fun e => s!"execute: {repr e}")
    checkedLoop p f fuel next (steps+1) trace

def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

end Libp2pAsm.Tests.Streams
