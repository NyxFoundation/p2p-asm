import Libp2pAsm.Spec.Codec.Der
import Libp2pAsm.Asm.Codec.Der
import Libp2pAsm.Rv64.Execution

namespace Libp2pAsm.Tests.Der
open Rv64
open Spec.Codec.Der

private def check (name : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"FAIL: {name}")

private def eqResult [BEq α] (a b : Except Error α) : Bool :=
  match a, b with
  | .ok x, .ok y => x == y
  | .error x, .error y => x == y
  | _, _ => false

private def specCases : IO Unit := do
  check "should encode minimal short-form length"
    (eqResult (encodeHeader 0x30 127) (.ok [0x30, 127]))
  check "should encode minimal long-form length"
    (eqResult (encodeHeader 4 128) (.ok [4, 0x81, 128]))
  check "should encode all eight bytes of a maximal length"
    (eqResult (encodeHeader 4 (2^64-1)) (.ok ([4, 0x88] ++ List.replicate 8 255)))
  check "should reject length overflow before truncation"
    (eqResult (decode [4, 0x89]) (.error .overflow))
  check "should reject unsupported high-tag-number form"
    (eqResult (decode [0x1f]) (.error .unsupportedTag))
  for bytes in [[4, 0x80], [4, 0xff], [4, 0x81, 0x7f],
      [4, 0x82, 0, 0x80], [0, 0], [0x20, 0]] do
    check "should reject malformed DER headers"
      (match decode bytes with | .error _ => true | _ => false)
  check "should decode only the first TLV"
    (eqResult (decode [4, 2, 0xaa, 0xbb, 5, 0]) (.ok ⟨4, 2, 2, 4⟩))

private def execute (body : SAsm.Stmt) (args : List Word)
    (memory : Memory) : IO State := do
  let .ok code := body.lower | throw (IO.userError "DER lowering failed")
  let initial : State := { pc := 0x10000, memory }
  let regs : List Reg := [.x10, .x11, .x12, .x13]
  let state := (regs.zip args).foldl (fun s (r, v) => s.setReg r v) initial
  let .ok result := runUntil ⟨0x10000, code⟩ 0 512 state
    | throw (IO.userError "DER instruction execution failed")
  return result.state

private def decodeCase (bytes : List UInt8) : IO Unit := do
  let memory : Memory := { regions := if bytes.isEmpty then #[] else #[
    { base := 0x20001, bytes := bytes.toArray, writable := false }] }
  let actual ← execute Asm.Codec.Der.decode
    [0x20001, BitVec.ofNat 64 bytes.length] memory
  let expected : List Word := match decode bytes with
    | .error e => [BitVec.ofNat 64 e.code, 0, 0, 0, 0]
    | .ok d => [0, BitVec.ofNat 64 d.tag.toNat, BitVec.ofNat 64 d.header,
        BitVec.ofNat 64 d.length, BitVec.ofNat 64 d.consumed]
  check "should match DER Spec status and all four result fields"
    ([.x10, .x11, .x12, .x13, .x14].map actual.getReg == expected)
  check "should never write input memory"
    (actual.memory.regions.map (fun r => (r.base, r.bytes, r.writable)) ==
      memory.regions.map (fun r => (r.base, r.bytes, r.writable)))

def run : IO Unit := do
  specCases
  for tag in [1, 2, 3, 4, 5, 6, 0x30, 0x31, 0xa0, 0xa3] do
    for n in [0, 1, 2, 126, 127, 128, 129, 255, 256, 257, 1024] do
      let .ok h := encodeHeader tag n | throw (IO.userError "valid DER header rejected")
      let bytes := h ++ List.replicate n 0x55
      decodeCase (bytes ++ [0xaa])
      for k in List.range h.length do decodeCase (bytes.take k)
      if n > 0 then decodeCase (bytes.take (bytes.length-1))
  for bytes in [[], [4], [0x1f], [4, 0x80], [4, 0xff], [4, 0x81, 127],
      [4, 0x82, 0, 128], [4, 0x88] ++ List.replicate 8 255,
      [0, 0], [0x20, 0], [4, 0x89]] do decodeCase bytes
  IO.println "PASS: should decode DER TLV headers with minimal lengths and exact bounds"

end Libp2pAsm.Tests.Der
