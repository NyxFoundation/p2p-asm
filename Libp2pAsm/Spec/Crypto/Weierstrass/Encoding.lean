import Libp2pAsm.Spec.Crypto.Weierstrass.Basic

namespace Libp2pAsm.Spec.Crypto.Weierstrass

def encodePoint (compressed : Bool) (p : Affine) : List UInt8 :=
  if compressed then [(2+p.y%2).toUInt8] ++ writeBE p.x
  else [4] ++ writeBE p.x ++ writeBE p.y

def decodePoint (c : Curve) (compressed : Bool) (b : List UInt8) : Option Affine := do
  if compressed then
    if b.length != 33 || (b[0]? != some 2 && b[0]? != some 3) then none else
    let x := readBE (b.drop 1)
    let yy := (x*x*x+c.a*x+c.b) % c.prime
    let y := powMod c.prime yy ((c.prime+1)/4)
    let y := if y%2 == (b.headD 0).toNat%2 then y else c.prime-y
    let p := Affine.mk x y
    if onCurve c p then some p else none
  else
    if b.length != 65 || b[0]? != some 4 then none else
    let p := Affine.mk (readBE ((b.drop 1).take 32)) (readBE (b.drop 33))
    if onCurve c p then some p else none

structure Signature where
  r : Nat
  s : Nat
  deriving BEq, DecidableEq, Repr

def validSignature (c : Curve) (lowS : Bool) (sig : Signature) : Bool :=
  validScalar c sig.r && validScalar c sig.s && (!lowS || sig.s ≤ c.order/2)

def compact (sig : Signature) : List UInt8 := writeBE sig.r ++ writeBE sig.s

def parseCompact (c : Curve) (lowS : Bool) (b : List UInt8) : Option Signature :=
  let sig := Signature.mk (readBE (b.take 32)) (readBE (b.drop 32))
  if b.length == 64 && validSignature c lowS sig then some sig else none

def integerDER (n : Nat) : List UInt8 :=
  let bs := (writeBE n).dropWhile (· == 0)
  let bs := if bs.isEmpty then [0] else if (bs.headD 0).toNat ≥ 128 then 0::bs else bs
  [2,bs.length.toUInt8] ++ bs

def der (sig : Signature) : List UInt8 :=
  let bs := integerDER sig.r ++ integerDER sig.s
  [0x30,bs.length.toUInt8] ++ bs

/-- Exact re-encoding enforces minimal unsigned positive integers, shortest
lengths, no trailing bytes, no overlong zero, no negative/empty integers. -/
def parseDER (c : Curve) (lowS : Bool) (b : List UInt8) : Option Signature := do
  if b.length < 8 || b.length > 72 then none else
  let lr := (b[3]?.getD 0).toNat
  if lr < 1 || lr > 33 || lr+6 > b.length then none else
  let ls := (b[5+lr]?.getD 0).toNat
  if ls < 1 || ls > 33 || lr+ls+6 != b.length then none else
  let sig := Signature.mk (readBE ((b.drop 4).take lr)) (readBE (b.drop (6+lr)))
  if validSignature c lowS sig && der sig == b then some sig else none

end Libp2pAsm.Spec.Crypto.Weierstrass
