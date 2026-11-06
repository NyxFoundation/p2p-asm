import Libp2pAsm.Asm.Clock
import Libp2pAsm.Spec.Clock
import Libp2pAsm.Codegen.Input
import Libp2pAsm.Rv64.Execution

namespace Libp2pAsm.Tests.ClockAsm

open Rv64 Spec.Clock

def stateWords (s : Spec.Clock.State) : List Word :=
  [BitVec.ofNat 64 s.mode, BitVec.ofNat 64 s.afterNs,
   BitVec.ofInt 64 s.seconds, BitVec.ofNat 64 s.nanos]

def sampleWords (s : Sample) : List Word :=
  [BitVec.ofNat 64 s.sourceStatus, BitVec.ofNat 64 s.beforeNs,
   BitVec.ofNat 64 s.afterNs, BitVec.ofInt 64 s.seconds, BitVec.ofNat 64 s.nanos]

def initial (s : Spec.Clock.State) (sample : Sample) (drift span : Nat) : Rv64.State :=
  let data := Codegen.wordBytes (stateWords s ++ [0xcafed00d] ++ sampleWords sample)
  let m : Memory := { regions := #[
    { base := 0x20000, bytes := data.data.extract 0 40, writable := true },
    { base := 0x20028, bytes := data.data.extract 40 80, writable := false }] }
  let machine : Rv64.State := {
    pc := 0x10000
    memory := m
    regs := Vector.ofFn fun i => BitVec.ofNat 64 (0xabc00000 + i.val) }
  let machine := machine.setReg .x1 0
  (((machine.setReg .x10 0x20000).setReg .x11 0x20028).setReg .x12
    (BitVec.ofNat 64 drift)).setReg .x13 (BitVec.ofNat 64 span)

def compare (s : Spec.Clock.State) (sample : Sample) (drift span : Nat) : IO Unit := do
  let .ok code := Asm.checkClock.lower | throw (IO.userError "Clock lowering failed.")
  let input := initial s sample drift span
  let .ok result := runUntil { base := 0x10000, code } 0 256 input
    | throw (IO.userError "Clock ASM trapped.")
  let (status, expected) := update s sample drift span
  unless result.state.getReg .x10 == BitVec.ofNat 64 status.code do
    throw (IO.userError s!"Clock status mismatch: {repr s}, {repr sample}, {drift}/{span}")
  let expectedBytes := (Codegen.wordBytes (stateWords expected ++ [0xcafed00d])).data
  let expectedMemory := input.memory.regions.modify 0 (fun r => { r with bytes := expectedBytes })
  let snapshot := fun (regions : Array Region) => regions.map fun r => (r.base, r.bytes, r.writable)
  unless snapshot result.state.memory.regions == snapshot expectedMemory do
    throw (IO.userError s!"Clock memory mismatch: {repr s}, {repr sample}")
  for r in [.x1, .x2, .x3, .x4, .x8, .x9, .x18, .x19, .x20, .x21,
      .x22, .x23, .x24, .x25, .x26, .x27] do
    unless result.state.getReg r == input.getReg r do
      throw (IO.userError "Clock ABI register mismatch.")

def run : IO Unit := do
  let sample : Sample := { beforeNs := 100, afterNs := 200, seconds := 1794000000, nanos := 500000000 }
  for mode in [0, 1, 2, 3, 4, 5, 2^64-1] do
    for status in [0, 1, 2, 3, 2^64-1] do
      compare { mode, afterNs := 50, seconds := sample.seconds, nanos := 500000000 }
        { sample with sourceStatus := status } 250000000 1000000
  for oldSec in [-(2^63), -1, 0, 1, 1794000000, 2^63-1] do
    for newSec in [-(2^63), -1, 0, 1, 1794000000, 2^63-1] do
      for ns in [0, 1, 499999999, 500000000, 999999999, 1000000000, 2^64-1] do
        compare { mode := 1, seconds := oldSec, nanos := 500000000 }
          { sample with seconds := newSec, nanos := ns } 250000000 1000000
  for drift in [0, 1, 250000000, 2^63, 2^64-1] do
    for mono in [0, 1, 250000000, 2^63, 2^64-1] do
      for seconds in [0, 1, 18446744073, 18446744074, 36893488147, 2^63-1] do
        compare { mode := 1 } { sample with beforeNs := mono, afterNs := mono, seconds, nanos := 0 } drift 1
  for before in [0, 1, 199, 200, 201, 1000200] do
    compare { mode := 1, afterNs := 200 } { sample with beforeNs := before } 250000000 1000000
  compare { mode := 4, nanos := 1000000000 } sample 250000000 1000000
  compare {} sample 1 2
  IO.println "PASS: should match clock ASM with signed epochs, 128-bit drift and recovery states"

end Libp2pAsm.Tests.ClockAsm
