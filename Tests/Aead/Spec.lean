import Libp2pAsm.Spec.Crypto.GCM.Basic

namespace Libp2pAsm.Tests.Aead

open Spec.Crypto

instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq x y := match x, y with
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

def check (name : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"FAIL: should {name}")

def hex (s : String) : Array UInt8 := Id.run do
  let chars := s.toList.filter (· != ' ')
  let mut out := #[]
  for i in List.range (chars.length / 2) do
    let nibble := fun c => if c ≤ '9' then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
    out := out.push (16 * nibble chars[2*i]! + nibble chars[2*i+1]!).toUInt8
  return out

/-- FIPS 197 Appendix B and C.1; SP 800-38A Appendix F.1.1. -/
def aesVectors : List (String × String × String) := [
  ("000102030405060708090a0b0c0d0e0f", "00112233445566778899aabbccddeeff", "69c4e0d86a7b0430d8cdb78070b4c55a"),
  ("2b7e151628aed2a6abf7158809cf4f3c", "3243f6a8885a308d313198a2e0370734", "3925841d02dc09fbdc118597196a0b32"),
  ("2b7e151628aed2a6abf7158809cf4f3c", "6bc1bee22e409f96e93d7e117393172a", "3ad77bb40d7a3660a89ecaf32466ef97"),
  ("2b7e151628aed2a6abf7158809cf4f3c", "ae2d8a571e03ac9c9eb76fac45af8e51", "f5d3d58503b9699de785895a96fdbaaf")]

/-- NIST GCM AES_GCM.pdf examples 1, 2, 5 plus the original GCM submission
zero-key known answers; 96-bit IV profile.
https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/AES_GCM.pdf
-/
def gcmVectors : List (String × String × String × String × String) := [
  ("00000000000000000000000000000000", "000000000000000000000000", "", "", "58e2fccefa7e3061367f1d57a4e7455a"),
  ("00000000000000000000000000000000", "000000000000000000000000", "", "00000000000000000000000000000000",
   "0388dace60b6a392f328c2b971b2fe78ab6e47d42cec13bdf53a67b21257bddf"),
  ("feffe9928665731c6d6a8f9467308308", "cafebabefacedbaddecaf888", "",
   "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255",
   "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f59854d5c2af327cd64a62cf35abd2ba6fab4"),
  ("feffe9928665731c6d6a8f9467308308", "cafebabefacedbaddecaf888", "3ad77bb40d7a3660a89ecaf32466ef97f5d3d585",
   "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39",
   "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091f07c2528eea2fca1211f905e1b6a881b")]

def runSpecs : IO Unit := do
  for (k, p, c) in aesVectors do
    check "match NIST AES vectors" (AES.encryptBytes (hex k) (hex p) == .ok (hex c))
  for (k, n, a, p, c) in gcmVectors do
    check "match NIST GCM seal vectors" (GCM.seal (hex k) (hex n) (hex a) (hex p) == .ok (hex c))
    check "match NIST GCM open vectors" (GCM.open (hex k) (hex n) (hex a) (hex c) == .ok (hex p))
  check "reject counter overflow" (GCM.validateLengths 12 0 (GCM.maxMessageBytes+1) == .error .messageTooLong)
  check "reject AAD bit-length overflow" (GCM.validateLengths 12 (2^61) 0 == .error .aadTooLong)
  for n in List.range 16 do
    check "reject every short tag before capacity" (GCM.openLength n 0 == .error .shortCiphertext)
  IO.println "PASS independent AES/GCM specifications and NIST vectors"

end Libp2pAsm.Tests.Aead

