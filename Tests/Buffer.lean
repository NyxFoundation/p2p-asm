import Libp2pAsm.Spec.Abi.Buffer
import Libp2pAsm.Asm.Buffer
import Libp2pAsm.Codegen.Input
import Libp2pAsm.Rv64.Execution

namespace Libp2pAsm.Tests.Buffer

open Spec.Abi Rv64

private def region : RegisteredRegion :=
  { generation := 7, base := 0x30000, capacity := 16, active := true, writable := true }

private def descriptor : BufferRef :=
  { slot := 0, generation := 7, offset := 4, length := 8 }

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL: {name}")

private def words (values : List Nat) : Array UInt8 :=
  (Codegen.wordBytes (values.map (BitVec.ofNat 64))).data

private def compare (r : RegisteredRegion) (ref : BufferRef) (write : Bool) : IO Unit := do
  let flags := (if r.active then 1 else 0) + (if r.writable then 2 else 0)
  let bytes := words [r.generation, r.base, r.capacity, flags,
    ref.slot, ref.generation, ref.offset, ref.length]
  let memory : Memory := { regions := #[{ base := 0x20000, bytes := bytes, writable := false }] }
  let s : State := { pc := 0x10000, memory := memory }
  let input := (((s.setReg .x10 0x20000).setReg .x11 0x20020).setReg .x12 1).setReg .x13
    (if write then 1 else 0)
  let .ok code := Asm.resolveBuffer.lower | throw (IO.userError "Buffer ASM layout failed.")
  let .ok done := runUntil { base := 0x10000, code := code } 0 128 input
    | throw (IO.userError "Buffer ASM trapped.")
  let (status, address, length) := match resolveBuffer #[r] ref write with
    | .ok span => (0, span.address, span.length)
    | .error e => (e.code, 0, 0)
  check "should match region resolution status, address and length"
    (done.state.getReg .x10 == BitVec.ofNat 64 status &&
      done.state.getReg .x11 == BitVec.ofNat 64 address &&
      done.state.getReg .x12 == BitVec.ofNat 64 length)

def run : IO Unit := do
  for capacity in [0, 1, 8, 16, 256] do
    for offset in [0, 1, 8, 16, 255, 256, 2^64-1] do
      for length in [0, 1, 8, 16, 255, 256, 2^64-1] do
        compare { region with capacity := capacity } { descriptor with offset, length } false
  for base in [0, 0x30000, 2^64-17, 2^64-16, 2^64-1] do
    compare { region with base := base } descriptor true
  compare { region with active := false } descriptor false
  compare { region with writable := false } descriptor false
  compare { region with writable := false } descriptor true
  compare region { descriptor with slot := 1 } false
  compare region { descriptor with generation := 6 } false
  compare region { descriptor with generation := 2^64-1 } false
  IO.println "PASS: should validate buffer generations, permissions and ordered non-wrapping ranges"

end Libp2pAsm.Tests.Buffer
