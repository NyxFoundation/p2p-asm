import Libp2pAsm.Asm.Crypto.SHA256
import Libp2pAsm.Asm.Crypto.SHA512
import Libp2pAsm.Asm.Crypto.HKDF
import Libp2pAsm.Asm.Crypto.TlsKdf
import Libp2pAsm.Spec.Crypto.HKDF
import Libp2pAsm.Spec.Crypto.SHA512
import Libp2pAsm.Spec.Crypto.TlsKdf
import Tests.AsmCrypto.Support
import Tests.AsmCrypto.Trace

namespace Libp2pAsm.Tests.HashCrypto
open Rv64
open AsmCrypto (check wordBytes readLE snapshot constants)

structure Case where
  a : Array UInt8
  b : Array UInt8
  params : Array UInt8
  start : State

def Case.field (c : Case) (i : Nat) : Nat := (readLE c.params (i*8)).toNat

def loadCase (dir : System.FilePath) (index : Nat) : IO Case := do
  let path := dir / s!"case-{index}"
  let before ← IO.FS.readBinFile (path / "before.bin")
  let sizes ← IO.FS.readBinFile (path / "sizes.bin")
  let mut regions := #[]
  let mut offset := 256
  for i in List.range 6 do
    let size := (readLE sizes.data (8*i)).toNat
    regions := regions.push ⟨BitVec.ofNat 64 ((i+1)*0x100000),
      (before.extract offset (offset+size)).data, i == 2 || i == 3 || i == 5⟩
    offset := offset+size
  check "consume complete case snapshot" (offset == before.size)
  let start : State := { pc := 0x10000, regs := Vector.ofFn (fun i => readLE before.data (i.val*8)), memory := ⟨regions⟩ }
  return ⟨(← IO.FS.readBinFile (path / "a.bin")).data,
    (← IO.FS.readBinFile (path / "b.bin")).data,
    (← IO.FS.readBinFile (path / "meta.bin")).data, start⟩

def reference (kind : String) (c : Case) : Except String (Array UInt8) := do
  let a := c.a.toList
  let b := c.b.toList
  let bytes ← if kind == "length512" then
      (Spec.Crypto.SHA512.padding (c.field 3)).map (fun suffix => suffix.drop (suffix.length-16)) |>.mapError reprStr
    else if kind == "tls" then
      (Spec.Crypto.TlsKdf.encodeLabel (c.field 3) a b).mapError reprStr
    else (match kind with
      | "sha256" => Spec.Crypto.SHA256.hash a
      | "sha512" => Spec.Crypto.SHA512.hash a
      | "hmac" => Spec.Crypto.HMAC.sha256 a b
      | "extract" => Spec.Crypto.HKDF.extract (some a) b
      | "expand" => Spec.Crypto.HKDF.expand a b (c.field 3)
      | _ => .error .invalidBlockLength).mapError reprStr
  return bytes.toArray

def replaced (bytes : Array UInt8) (offset : Nat) (payload : Array UInt8) : Array UInt8 :=
  bytes.extract 0 offset ++ payload ++ bytes.extract (offset+payload.size) bytes.size

def expected (c : Case) (result : Array UInt8) : State :=
  let regions := c.start.memory.regions.mapIdx fun i r =>
    let bytes := if i == 2 && c.field 0 == 0 then replaced r.bytes (8+c.field 5) result
      else if i == 3 && c.field 1 > 0 then replaced r.bytes 8 (Array.replicate (c.field 1) 0)
      else if i == 5 && c.field 2 > 0 then
        replaced r.bytes (416-c.field 2) (Array.replicate (c.field 2) 0)
      else r.bytes
    { r with bytes := bytes }
  let state := Asm.Crypto.Sha2.cleared.foldl (fun s r => s.setReg r 0) c.start
  { state.setReg .x10 (BitVec.ofNat 64 (c.field 0)) with pc := 0x80000, memory := ⟨regions⟩ }

def body (kind : String) : Except String SAsm.Stmt := match kind with
  | "length512" => .ok (Asm.sequence [Asm.Crypto.Whole.lengthField .sha512 .x11 .x10,
      Asm.Crypto.Util.finish 0])
  | "sha256" => .ok Asm.Crypto.SHA256.hash
  | "sha512" => .ok Asm.Crypto.SHA512.hash
  | "hmac" => Asm.Crypto.HMAC.sha256
  | "extract" => Asm.Crypto.HKDF.extract
  | "expand" => Asm.Crypto.HKDF.expand
  | "tls" => .ok Asm.Crypto.TlsKdf.encodeLabel
  | _ => .error "unknown algorithm"

def variant (kind : String) : Asm.Crypto.Sha2.Variant :=
  if kind == "sha512" then .sha512 else .sha256

end Libp2pAsm.Tests.HashCrypto
