import Libp2pAsm.Asm.Codec.QuicVarint
import Libp2pAsm.Asm.Codec.UnsignedVarint
import Libp2pAsm.Rv64.Execution
import Libp2pAsm.Spec.Codec.QuicVarint
import Libp2pAsm.Spec.Codec.UnsignedVarint

namespace Libp2pAsm.Tests.AsmCodec

open Rv64

private def errorCode : Spec.Codec.Error → Word
  | .truncated => 1 | .overflow => 2 | .nonMinimal => 3

private def execute (body : SAsm.Stmt) (a0 a1 a2 : Word) (memory : Memory) : IO State := do
  let .ok code := body.lower | throw (IO.userError "ASM layout rejected.")
  let state : State := { pc := 0x10000, memory := memory }
  let initial := ((state.setReg .x10 a0).setReg .x11 a1).setReg .x12 a2
  let .ok done := runUntil { base := 0x10000, code := code } 0 512 initial
    | throw (IO.userError "ASM codec trapped or exceeded its test budget.")
  return done.state

private def check (name : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"FAIL: {name}")

private def encoder (body : SAsm.Stmt)
    (spec : Nat → Except Spec.Codec.Error (List UInt8)) (value capacity : Nat) : IO Unit := do
  let original : Array UInt8 := Array.replicate (capacity + 2) 0xaa
  let memory : Memory := { regions := #[{ base := 0x20000, bytes := original, writable := true }] }
  let state ← execute body (BitVec.ofNat 64 value) 0x20001 (BitVec.ofNat 64 capacity) memory
  let (status, bytes) := match spec value with
    | .error e => (errorCode e, [])
    | .ok bytes => if bytes.length ≤ capacity then (0, bytes) else (1, [])
  check "should match the encoder status and byte count"
    (state.getReg .x10 == status && state.getReg .x11 == BitVec.ofNat 64 bytes.length)
  let expected := #[0xaa] ++ bytes.toArray ++ Array.replicate (capacity - bytes.length + 1) 0xaa
  check "should write only encoded bytes and preserve both buffer guards"
    (match state.memory.regions[0]? with | some region => region.bytes == expected | none => false)

private def decoder (body : SAsm.Stmt)
    (spec : List UInt8 → Except Spec.Codec.Error Spec.Codec.Decoded) (bytes : List UInt8) :
    IO Unit := do
  let memory : Memory := if bytes.isEmpty then {} else
    { regions := #[{ base := 0x20000, bytes := bytes.toArray, writable := false }] }
  let state ← execute body 0x20000 (BitVec.ofNat 64 bytes.length) 0 memory
  let (status, value, consumed) := match spec bytes with
    | .error e => (errorCode e, 0, 0)
    | .ok d => (0, d.value, d.consumed)
  check "should match the decoder status, value and exact consumed length"
    (state.getReg .x10 == status && state.getReg .x11 == BitVec.ofNat 64 value &&
      state.getReg .x12 == BitVec.ofNat 64 consumed)

private def suite (enc dec : SAsm.Stmt)
    (specEnc : Nat → Except Spec.Codec.Error (List UInt8))
    (specDec : List UInt8 → Except Spec.Codec.Error Spec.Codec.Decoded) : IO Unit := do
  let values := List.range 256 ++ [16383, 16384, 2^30-1, 2^30, 2^56, 2^62-1, 2^62, 2^63-1, 2^63, 2^64-1]
  for value in values do
    for capacity in [0, 1, 2, 3, 4, 7, 8, 9, 10] do encoder enc specEnc value capacity
    if let .ok bytes := specEnc value then
      decoder dec specDec (bytes ++ [0xaa])
      for n in List.range bytes.length do decoder dec specDec (bytes.take n)

def run : IO Unit := do
  suite Asm.Codec.QuicVarint.encode Asm.Codec.QuicVarint.decode
    Spec.Codec.QuicVarint.encode Spec.Codec.QuicVarint.decode
  suite Asm.Codec.UnsignedVarint.encode Asm.Codec.UnsignedVarint.decode
    Spec.Codec.UnsignedVarint.encode Spec.Codec.UnsignedVarint.decode
  for bytes in [[0x40, 0], [0x80, 0, 0, 1], [0xc0, 0, 0, 0, 0, 0, 0, 1]] do
    decoder Asm.Codec.QuicVarint.decode Spec.Codec.QuicVarint.decode bytes
  for bytes in [[0x80, 0], [0x81, 0], List.replicate 9 0x80, List.replicate 10 0xff] do
    decoder Asm.Codec.UnsignedVarint.decode Spec.Codec.UnsignedVarint.decode bytes
  IO.println "PASS: should match both varint ASM implementations against their specs and buffer guards"

end Libp2pAsm.Tests.AsmCodec
