import Libp2pAsm.Spec.Crypto.HKDF
import Tests.Crypto.Support

/-!
RFC 5869 Appendix A.1-A.3: all SHA-256 extract/expand test vectors.
https://www.rfc-editor.org/rfc/rfc5869.html#appendix-A
Copyright (c) 2010 IETF Trust and the persons identified as the document
authors. All rights reserved. See LICENSE-RFC.txt for the Simplified BSD license.
-/

namespace Libp2pAsm.Tests.Crypto

open Spec.Crypto

private def case1Prk : String :=
  "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5"

private def case1Okm : String :=
  "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865"

private def rfc5869Case1 : IO Unit := do
  let ikm := List.replicate 22 0x0b
  let salt := byteRange 0 13
  let info := byteRange 0xf0 10
  expectHex "should match RFC 5869 A.1 PRK when extracting with explicit salt"
    (HKDF.extract (some salt) ikm) case1Prk
  -- Expand is fed the independently published PRK, not our extract output.
  expectHex "should match RFC 5869 A.1 OKM when expanding the published PRK"
    (HKDF.expand (← hex case1Prk) info 42) case1Okm
  expectHex "should match RFC 5869 A.1 OKM when deriving end to end"
    (HKDF.derive (some salt) ikm info 42) case1Okm

private def rfc5869Case2 : IO Unit := do
  let ikm := byteRange 0 80
  let salt := byteRange 0x60 80
  let info := byteRange 0xb0 80
  let expectedPrk := "06a6b88c5853361a06104c9ceb35b45cef760014904671014a193f40c15fc244"
  let expectedOkm := "b11e398dc80327a1c8e7f78c596a49344f012eda2d4efad8a050cc4c19afa97c" ++
    "59045a99cac7827271cb41c65e590e09da3275600c2f09b8367793a9aca3db71" ++
    "cc30c58179ec3e87c14c01d5c1f3434f1d87"
  expectHex "should match RFC 5869 A.2 PRK when salt exceeds one SHA block"
    (HKDF.extract (some salt) ikm) expectedPrk
  expectHex "should match RFC 5869 A.2 OKM when expanding across three blocks"
    (HKDF.expand (← hex expectedPrk) info 82) expectedOkm
  expectHex "should match RFC 5869 A.2 OKM when deriving end to end"
    (HKDF.derive (some salt) ikm info 82) expectedOkm

private def rfc5869Case3 : IO Unit := do
  let ikm := List.replicate 22 0x0b
  let expectedPrk := "19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04"
  let expectedOkm := "8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8"
  for salt in [some [], none, some (List.replicate 32 0)] do
    expectHex "should match RFC 5869 A.3 PRK when salt is empty, absent or default zeros"
      (HKDF.extract salt ikm) expectedPrk
    expectHex "should match RFC 5869 A.3 OKM when deriving with default salt"
      (HKDF.derive salt ikm [] 42) expectedOkm
  expectHex "should match RFC 5869 A.3 OKM when info is empty"
    (HKDF.expand (← hex expectedPrk) [] 42) expectedOkm

private def expandBoundaries : IO Unit := do
  let prk ← hex case1Prk
  let info := byteRange 0xf0 10
  let expected ← hex case1Okm
  for length in [0, 1, 31, 32, 33, 42] do
    let actual ← unwrap "HKDF prefix" (HKDF.expand prk info length)
    check "should match the published OKM prefix when output length crosses a block"
      (actual == expected.take length)
  let maximum ← unwrap "maximum HKDF length" (HKDF.expand prk info 8160)
  check "should produce exactly 255 blocks when the maximum length is requested"
    (maximum.length == 8160 && maximum.take 42 == expected)
  for length in [8161, 8192, 2^64] do
    expectError "should reject HKDF expand when more than 255 blocks are requested"
      (HKDF.expand prk info length) .outputTooLong
    expectError "should reject HKDF derive when more than 255 blocks are requested"
      (HKDF.derive none [] info length) .outputTooLong
  for length in [0, 1, 31] do
    expectError "should reject a short PRK when expanding"
      (HKDF.expand (List.replicate length 0) [] 1) .prkTooShort
  expectError "should validate the PRK even when output length is zero"
    (HKDF.expand [] [] 0) .prkTooShort
  expectHex "should return no output when deriving length zero" (HKDF.derive none [] [] 0) ""

def runHKDF : IO Unit := do
  rfc5869Case1
  rfc5869Case2
  rfc5869Case3
  expandBoundaries
  IO.println "PASS: HKDF-SHA256: RFC 5869 A.1-A.3, default salt, zero length and 255-block limit"

end Libp2pAsm.Tests.Crypto
