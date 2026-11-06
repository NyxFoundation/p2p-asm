import Std

/-! Independent natural-number, affine specifications. Not a runtime implementation. -/
namespace Libp2pAsm.Spec.Crypto.Weierstrass

inductive Curve where
  | p256 | secp256k1
  deriving BEq, DecidableEq, Repr

def Curve.prime : Curve → Nat
  | .p256 => 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
  | .secp256k1 => 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

def Curve.order : Curve → Nat
  | .p256 => 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
  | .secp256k1 => 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

def Curve.a (c : Curve) : Nat := if c == .p256 then c.prime - 3 else 0

def Curve.b : Curve → Nat
  | .p256 => 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
  | .secp256k1 => 7

structure Affine where
  x : Nat
  y : Nat
  deriving BEq, DecidableEq, Repr

abbrev Point := Option Affine

def Curve.generator : Curve → Affine
  | .p256 => ⟨0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296,
      0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5⟩
  | .secp256k1 => ⟨0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,
      0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8⟩

def powMod (m x e : Nat) : Nat :=
  if e = 0 then 1 % m else
    let h := powMod m x (e / 2)
    (h*h*(if e % 2 = 0 then 1 else x)) % m
termination_by e

def subMod (m x y : Nat) : Nat := (x + m - y % m) % m
def inv (m x : Nat) : Nat := powMod m x (m-2)
def validScalar (c : Curve) (s : Nat) : Bool := 0 < s && s < c.order
def onCurve (c : Curve) (p : Affine) : Bool :=
  p.x < c.prime && p.y < c.prime &&
    p.y*p.y % c.prime == (p.x*p.x*p.x+c.a*p.x+c.b) % c.prime

def add (c : Curve) (p q : Point) : Point := do
  match p, q with
  | none, _ => q
  | _, none => p
  | some p, some q =>
    if p.x == q.x && (p.y+q.y) % c.prime == 0 then none else
    let slope := if p == q then (3*p.x*p.x+c.a)*inv c.prime (2*p.y) % c.prime
      else subMod c.prime q.y p.y * inv c.prime (subMod c.prime q.x p.x) % c.prime
    let x := subMod c.prime (subMod c.prime (slope*slope) p.x) q.x
    some ⟨x, subMod c.prime (slope * subMod c.prime p.x x) p.y⟩

def mul (c : Curve) (s : Nat) (p : Point) : Point :=
  if s = 0 then none else
    let h := mul c (s/2) p
    let d := add c h h
    if s % 2 = 0 then d else add c d p
termination_by s

def readBE (xs : List UInt8) : Nat := xs.foldl (fun n b => 256*n+b.toNat) 0
def writeBE (n : Nat) : List UInt8 :=
  (List.range 32).map fun i => (n / 2^(8*(31-i)) % 256).toUInt8

end Libp2pAsm.Spec.Crypto.Weierstrass
