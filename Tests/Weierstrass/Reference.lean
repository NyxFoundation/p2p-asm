import Tests.Weierstrass.Support

namespace Libp2pAsm.Tests.Weierstrass
open Spec.Crypto.Weierstrass

def metadata (f : Fixture) (offset : Nat) : Nat :=
  ((f.regions[1]!).extract (8+offset) (16+offset)).toList.reverse.foldl (fun n b => 256*n+b) 0

def inputBytes (f : Fixture) (offset : Nat) : List UInt8 :=
  let ptr := metadata f offset
  let region := (ptr-0x200000)/0x10000
  let start := ptr-base region
  ((f.regions[region]!).extract start (start+metadata f (offset+8))).toList.map Nat.toUInt8

def reference (c : Curve) (kind : String) (f : Fixture) : IO Unit := do
  if [1,4,5].contains f.status then return
  let out := f.expected.toList.map Nat.toUInt8
  let d := readBE (inputBytes f 0)
  if kind == "public" then
    match publicKey c d with
    | .ok p => check "pure affine key agreement" (f.status == 0 && encodePoint (c == .secp256k1) p == out)
    | .error _ => check "pure key domain rejection" (f.status == 8)
  if kind == "ecdh" then
    match decodePoint c (c == .secp256k1) (inputBytes f 16) with
    | none => check "pure point rejection" (f.status == 9)
    | some p => match ecdh c d p with
      | .ok xs => check "pure affine ECDH agreement" (f.status == 0 && xs == out)
      | .error _ => check "pure ECDH domain rejection" (f.status == 8)
  if kind == "sign" || kind == "signcompact" then
    match sign c d (inputBytes f 32) with
    | .error .invalidScalar => check "pure invalid signer" (f.status == 8)
    | .error .nonceRejected => check "pure nonce failure" (f.status == 10)
    | .error _ => throw (IO.userError "unexpected pure signing error")
    | .ok sig =>
      let xs := if kind == "signcompact" then compact sig else
        (wordBytes [(der sig).length]).toList ++ der sig ++ List.replicate (72-(der sig).length) 0
      check "pure RFC6979 signature agreement" (f.status == 0 && xs == out)
  if kind == "signnonce" then
    match nonceInit c d (inputBytes f 32) >>= nonceNext with
    | .ok (k,_) => check "pure RFC6979 candidate" (writeBE k == out)
    | .error _ => throw (IO.userError "pure nonce initialization failed")
  if kind.startsWith "verify" then
    let sig := if kind == "verifycompact" then parseCompact c false (inputBytes f 48)
      else parseDER c (kind == "verifylow") (inputBytes f 48)
    let pk := decodePoint c (c == .secp256k1) (inputBytes f 16)
    let good := match pk,sig with
      | some q,some s => verify c (kind == "verifylow") q (inputBytes f 32) s
      | _,_ => false
    check "pure ECDSA verification agreement" (good == (f.status == 0))

end Libp2pAsm.Tests.Weierstrass
