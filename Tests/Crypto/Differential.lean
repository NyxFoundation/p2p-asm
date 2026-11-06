import Libp2pAsm.Spec.Crypto.SHA512
import Libp2pAsm.Spec.Crypto.HKDF
import Tests.Crypto.Support

/-!
Optional test-only data emitter for differential.py. All inputs are public,
deterministic fixtures. The specification never invokes an external implementation.
This target is deliberately separate from the official-vector test runner.
-/

namespace Libp2pAsm.Tests.Crypto.Differential

open Spec.Crypto

private def fixture (length seed : Nat) : Bytes :=
  (List.range length).map (fun i => ((i*37 + seed*17 + i/7) % 256).toUInt8)

private def toHex (bytes : Bytes) : String :=
  String.ofList (bytes.flatMap fun b =>
    [Char.ofNat (if b.toNat/16 < 10 then 48 + b.toNat/16 else 87 + b.toNat/16),
     Char.ofNat (if b.toNat%16 < 10 then 48 + b.toNat%16 else 87 + b.toNat%16)])

private def emit (label : String) (result : Except Error Bytes) : IO Unit := do
  let bytes ← unwrap label result
  IO.println s!"{label}:{toHex bytes}"

private def hashes : IO Unit := do
  for length in List.range 261 ++ [511, 512, 513, 1024, 4097] do
    let message := fixture length 1
    emit s!"sha256:{length}" (SHA256.hash message)
    emit s!"sha512:{length}" (SHA512.hash message)

private def macs : IO Unit := do
  for keyLength in [0, 1, 31, 32, 63, 64, 65, 127, 128, 131] do
    for messageLength in [0, 1, 55, 56, 63, 64, 65, 111, 112, 127, 128, 129] do
      emit s!"hmac:{keyLength}:{messageLength}"
        (HMAC.sha256 (fixture keyLength 2) (fixture messageLength 3))

private def kdfs : IO Unit := do
  for prkLength in [32, 33, 64, 65, 131] do
    for length in [0, 1, 31, 32, 33, 63, 64, 65, 82, 8160] do
      emit s!"expand:{prkLength}:{length}"
        (HKDF.expand (fixture prkLength 4) (fixture 17 5) length)
  for saltLength in [0, 1, 32, 64, 65, 131] do
    emit s!"extract:{saltLength}"
      (HKDF.extract (some (fixture saltLength 6)) (fixture 257 7))
  emit "extract-default" (HKDF.extract none (fixture 257 7))

def run : IO Unit := do
  hashes
  macs
  kdfs

end Libp2pAsm.Tests.Crypto.Differential

def main : IO Unit := Libp2pAsm.Tests.Crypto.Differential.run
