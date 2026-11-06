import Libp2pAsm.Spec.Crypto.SHA256
import Libp2pAsm.Spec.Crypto.SHA512
import Tests.Crypto.SHA256Vectors
import Tests.Crypto.SHA512Vectors

namespace Libp2pAsm.Tests.Crypto

open Spec.Crypto

/- NIST examples, "One Block Message Sample" and "Two Block Message Sample":
https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA256.pdf
https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA512.pdf
-/
private def publishedExamples : IO Unit := do
  expectHex "should match NIST SHA-256 when hashing abc" (SHA256.hash (ascii "abc"))
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
  expectHex "should match NIST SHA-512 when hashing abc" (SHA512.hash (ascii "abc"))
    ("ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a" ++
      "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f")
  expectHex "should match NIST SHA-256 when padding requires two blocks"
    (SHA256.hash (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"))
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
  expectHex "should match NIST SHA-512 when padding requires two blocks"
    (SHA512.hash (ascii ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmn" ++
      "hijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu")))
    ("8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018" ++
      "501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909")

private def paddingTransitions : IO Unit := do
  for (length, expectedSize) in [(0,64), (3,61), (55,9), (56,72), (57,71), (63,65), (64,64)] do
    let suffix ← unwrap "SHA-256 padding" (SHA256.padding length)
    check "should align SHA-256 blocks when the padding boundary is crossed"
      (suffix.length == expectedSize && (length + suffix.length) % 64 == 0)
    check "should append 0x80 and zeros before the SHA-256 length field"
      (suffix.take (suffix.length - 8) == 0x80 :: List.replicate (suffix.length - 9) 0)
  for (length, expectedSize) in [(0,128), (3,125), (111,17), (112,144), (113,143), (127,129), (128,128)] do
    let suffix ← unwrap "SHA-512 padding" (SHA512.padding length)
    check "should align SHA-512 blocks when the padding boundary is crossed"
      (suffix.length == expectedSize && (length + suffix.length) % 128 == 0)
    check "should append 0x80 and zeros before the SHA-512 length field"
      (suffix.take (suffix.length - 16) == 0x80 :: List.replicate (suffix.length - 17) 0)
  let p256 ← unwrap "SHA-256 length field" (SHA256.padding 3)
  let p512 ← unwrap "SHA-512 length field" (SHA512.padding 3)
  check "should encode SHA-256 bit length in big endian when input has three bytes"
    (p256.drop (p256.length - 8) == (← hex "0000000000000018"))
  check "should encode SHA-512 bit length in big endian when input has three bytes"
    (p512.drop (p512.length - 16) == (← hex "00000000000000000000000000000018"))

/-- Test theoretical length boundaries without allocating impossibly large messages. -/
private def lengthLimits : IO Unit := do
  for n in [2^61, 2^61 + 1, 2^64] do
    expectError "should reject SHA-256 padding when its bit length cannot fit"
      (SHA256.padding n) .messageTooLong
  for n in [2^125, 2^125 + 1, 2^128] do
    expectError "should reject SHA-512 padding when its bit length cannot fit"
      (SHA512.padding n) .messageTooLong
  let last256 ← unwrap "maximum SHA-256 length" (SHA256.padding (2^61 - 1))
  check "should preserve all SHA-256 length bits when just below the limit"
    (last256.drop (last256.length - 8) == (← hex "fffffffffffffff8"))
  let last512 ← unwrap "maximum SHA-512 length" (SHA512.padding (2^125 - 1))
  check "should preserve all SHA-512 length bits when just below the limit"
    (last512.drop (last512.length - 16) == (← hex "fffffffffffffffffffffffffffffff8"))
  let high512 ← unwrap "SHA-512 high length word" (SHA512.padding (2^61))
  check "should retain the SHA-512 high word when bit length reaches 2^64"
    (high512.drop (high512.length - 16) == (← hex "00000000000000010000000000000000"))
  check "should reject partial blocks when compression input is incomplete"
    (match Sha2.foldBlocks 64 (by decide) SHA256.compress SHA256.initial [1] with
      | .error .invalidBlockLength => true | _ => false)

def runSHA : IO Unit := do
  publishedExamples
  for v in SHA256Vectors.all do runHashVector SHA256.hash v
  for v in SHA512Vectors.all do runHashVector SHA512.hash v
  paddingTransitions
  lengthLimits
  IO.println "PASS: SHA-256/SHA-512: 22 published vectors, padding transitions and length limits"

end Libp2pAsm.Tests.Crypto
