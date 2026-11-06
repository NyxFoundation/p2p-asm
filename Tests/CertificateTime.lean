import Libp2pAsm.Spec.Identity.Time
import Libp2pAsm.Asm.Identity.Time
import Libp2pAsm.Rv64.Execution

namespace Libp2pAsm.Tests.CertificateTime

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL: {name}")

private def ascii (s : String) : List UInt8 := s.toUTF8.data.toList

private def edgeAddresses : IO Unit := do
  let payload := (ascii "700101000000Z").toArray
  let ptr := BitVec.ofNat 64 (2^64-payload.size)
  let state : Rv64.State := {
    pc := 0x10000
    memory := ⟨#[⟨ptr, payload, false⟩]⟩ }
  let state := state.setReg .x10 23 |>.setReg .x11 ptr |>.setReg .x12 13
  let .ok code := Asm.Identity.Time.decode.lower | throw (IO.userError "decode layout")
  let .ok done := Rv64.runUntil ⟨0x10000, code⟩ 0 5000 state
    | throw (IO.userError "decode address-boundary trap")
  check "should read a valid range ending at2^64" (done.state.getReg .x10 == 0 &&
    done.state.getReg .x11 == 0)
  let out := BitVec.ofNat 64 (2^64-15)
  let initial : Rv64.State := {
    pc := 0x10000
    memory := ⟨#[⟨out, Array.replicate 15 0xcc, true⟩]⟩ }
  let initial := initial.setReg .x11 out |>.setReg .x12 15
  let .ok code := Asm.Identity.Time.encode.lower | throw (IO.userError "encode layout")
  let .ok done := Rv64.runUntil ⟨0x10000, code⟩ 0 5000 initial
    | throw (IO.userError "encode address-boundary trap")
  check "should write a valid range ending at2^64" (done.state.getReg .x10 == 0 &&
    done.state.getReg .x11 == 15 &&
    (done.state.memory.regions[0]?.map (·.bytes.toList)) == some ([23, 13] ++ ascii "700101000000Z"))

def run : IO Unit := do
  edgeAddresses
  check "should lower the signed128 certificate validity checker" Asm.Identity.Time.validity.lower.isOk
  for (tag, text, seconds) in [
      (0x17, "700101000000Z", (0 : Int)),
      (0x17, "991231235959Z", 946684799),
      (0x17, "000229000000Z", 951782400),
      (0x18, "00010101000000Z", -62135596800),
      (0x18, "99991231235959Z", 253402300799)] do
    check "should decode canonical UTC/generalized certificate time"
      (match Spec.Identity.Time.decode tag (ascii text) with
        | .ok s => s == seconds | _ => false)
  for text in ["000230000000Z", "010229000000Z", "001300000000Z",
      "000101240000Z", "000101000060Z", "000101000000+", "0x0101000000Z"] do
    check "should reject invalid dates without normalizing them"
      (match Spec.Identity.Time.decode 0x17 (ascii text) with | .error _ => true | _ => false)
  IO.println "PASS: should parse X509 UTC/generalized times with exact Gregorian bounds"

end Libp2pAsm.Tests.CertificateTime
