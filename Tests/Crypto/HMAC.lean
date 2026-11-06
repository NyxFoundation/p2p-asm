import Libp2pAsm.Spec.Crypto.HMAC
import Tests.Crypto.Support

/-!
RFC 4231 sections 4.2 through 4.8, all seven HMAC-SHA-256 cases.
https://www.rfc-editor.org/rfc/rfc4231.html#section-4
Copyright (C) The Internet Society (2005). Test vectors may be used for
conformance testing as stated in the RFC; see LICENSE-RFC.txt for notices.
Case 5 publishes only a 16-byte truncated MAC, so only that prefix is asserted.
-/

namespace Libp2pAsm.Tests.Crypto

open Spec.Crypto

private def rfc4231Short : IO Unit := do
  expectHex "should match RFC 4231 case 1 when key is twenty 0x0b bytes"
    (HMAC.sha256 (List.replicate 20 0x0b) (ascii "Hi There"))
    "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"
  expectHex "should match RFC 4231 case 2 when key is Jefe"
    (HMAC.sha256 (ascii "Jefe") (ascii "what do ya want for nothing?"))
    "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"
  expectHex "should match RFC 4231 case 3 when data is fifty 0xdd bytes"
    (HMAC.sha256 (List.replicate 20 0xaa) (List.replicate 50 0xdd))
    "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe"
  expectHex "should match RFC 4231 case 4 when key bytes ascend"
    (HMAC.sha256 (byteRange 1 25) (List.replicate 50 0xcd))
    "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b"
  let full ← unwrap "RFC 4231 case 5"
    (HMAC.sha256 (List.replicate 20 0x0c) (ascii "Test With Truncation"))
  check "should produce a full MAC when RFC 4231 case 5 only publishes its prefix"
    (full.length == 32)
  expectHex "should match RFC 4231 case 5 when truncated to 128 bits" (.ok (full.take 16))
    "a3b6167473100ee06e0c796c2955552b"

private def rfc4231Long : IO Unit := do
  let key := List.replicate 131 0xaa
  expectHex "should match RFC 4231 case 6 when key must first be hashed"
    (HMAC.sha256 key (ascii "Test Using Larger Than Block-Size Key - Hash Key First"))
    "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"
  expectHex "should match RFC 4231 case 7 when both key and data exceed a block"
    (HMAC.sha256 key (ascii ("This is a test using a larger than block-size key and a larger " ++
      "than block-size data. The key needs to be hashed before being used by the HMAC algorithm.")))
    "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2"

/- NIST HMAC-SHA256 worked example, key length = 64, full 32-byte tag:
https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/HMAC_SHA256.pdf
-/
private def blockKey : IO Unit := do
  expectHex "should match NIST HMAC when the key occupies exactly one block"
    (HMAC.sha256 (byteRange 0 64) (ascii "Sample message for keylen=blocklen"))
    "8bb9a1db9806f20df7f77b82138c7914d174d59e13dc4d0169c9057b133e1d62"

private def keyBoundaries : IO Unit := do
  let message := ascii "Hi There"
  let expected := "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"
  -- RFC 2104 zero-padding equivalence, anchored to RFC 4231 case 1.
  for n in [0, 1, 43, 44] do
    expectHex "should preserve the published MAC when short keys have explicit zero padding"
      (HMAC.sha256 (List.replicate 20 0x0b ++ List.replicate n 0) message) expected
  let emptyKey ← unwrap "empty-key HMAC" (HMAC.sha256 [] message)
  let zeroKey ← unwrap "zero-block-key HMAC" (HMAC.sha256 (List.replicate 64 0) message)
  check "should support an empty key when HMAC zero-padding makes it a zero block"
    (emptyKey.length == 32 && emptyKey == zeroKey)
  for n in [0, 1, 63, 64, 65, 131] do
    let normalized ← unwrap "key normalization" (HMAC.normalizeKey (byteRange 0 n))
    check "should normalize to exactly one block when key length crosses 64 bytes"
      (normalized.length == 64)

def runHMAC : IO Unit := do
  rfc4231Short
  rfc4231Long
  blockKey
  keyBoundaries
  IO.println "PASS: HMAC-SHA256: RFC 4231 cases 1-7, NIST block-sized key and key boundaries"

end Libp2pAsm.Tests.Crypto
