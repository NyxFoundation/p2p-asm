import Libp2pAsm.Spec.Crypto.Curve25519.Field
import Libp2pAsm.Spec.Crypto.SHA512

namespace Libp2pAsm.Spec.Crypto.Curve25519.Ed25519

structure Point where
  x : Nat
  y : Nat
  z : Nat
  t : Nat
  deriving Repr

def identity : Point := ⟨0, 1, 1, 0⟩
def base : Point :=
  let x := 15112221349535400772501151409588531511454012693041857206046113283949847762202
  let y := 46316835694926478169428394003475163141307993866256225615783033603165251855960
  ⟨x, y, 1, mul x y⟩

/-- Complete extended-coordinate addition from RFC 8032 section 6. -/
def pointAdd (p q : Point) : Point :=
  let a := mul (sub p.y p.x) (sub q.y q.x)
  let b := mul (add p.y p.x) (add q.y q.x)
  let c := mul (mul p.t q.t) (add d d)
  let dd := add (mul p.z q.z) (mul p.z q.z)
  let e := sub b a
  let f := sub dd c
  let g := add dd c
  let h := add b a
  ⟨mul e f, mul g h, mul f g, mul e h⟩

def scalarMul (p : Point) (s : Nat) : Point :=
  (List.range 256).foldl (fun q i =>
    let doubled := pointAdd q q
    if s.testBit (255-i) then pointAdd doubled p else doubled) identity

def equal (p q : Point) : Bool :=
  mul p.x q.z == mul q.x p.z && mul p.y q.z == mul q.y p.z

def encode (p : Point) : Bytes :=
  let iz := inverse p.z
  encodeLE (mul p.y iz + (mul p.x iz % 2) * 2^255) 32

/-- Canonical y, valid square root, and no negative zero. -/
def decode (bs : Bytes) : Except Error Point := do
  if bs.length != 32 then throw .invalidLength
  let word := decodeLE bs
  let y := word % 2^255
  let sign := word / 2^255
  if y ≥ prime then throw .noncanonical
  let yy := mul y y
  let xx := mul (sub yy 1) (inverse (add (mul d yy) 1))
  let x := power xx ((prime+3)/8)
  let x := if mul x x == xx then x else mul x sqrtM1
  if mul x x != xx then throw .invalidPoint
  if x == 0 && sign != 0 then throw .noncanonical
  let x := if x % 2 == sign then x else sub 0 x
  return ⟨x,y,1,mul x y⟩

def hash (bs : Bytes) : Except Error Bytes :=
  (SHA512.hash bs).mapError (fun _ => .messageTooLong)

def publicKey (seed : Bytes) : Except Error Bytes := do
  if seed.length != 32 then throw .invalidLength
  let h ← hash seed
  return encode (scalarMul base (clamp (h.take 32)))

def sign (seed message : Bytes) : Except Error Bytes := do
  if seed.length != 32 then throw .invalidLength
  let h ← hash seed
  let a := clamp (h.take 32)
  let key := encode (scalarMul base a)
  let r := decodeLE (← hash (h.drop 32 ++ message)) % order
  let encodedR := encode (scalarMul base r)
  let k := decodeLE (← hash (encodedR ++ key ++ message)) % order
  return encodedR ++ encodeLE ((r + k*a) % order) 32

/-- Strict policy: canonical A/R/S, nonidentity prime-order A and R, uncofactored
[S]B = R + [k]A. Rejects torsion and mixed-order points, not just small order. -/
def verify (key message signature : Bytes) : Except Error Unit := do
  if key.length != 32 || signature.length != 64 then throw .invalidLength
  let s := decodeLE (signature.drop 32)
  if s ≥ order then throw .noncanonical
  let a ← decode key
  let r ← decode (signature.take 32)
  if equal a identity || equal r identity ||
      !equal (scalarMul a order) identity || !equal (scalarMul r order) identity then
    throw .smallOrder
  let k := decodeLE (← hash (signature.take 32 ++ key ++ message)) % order
  unless equal (scalarMul base s) (pointAdd r (scalarMul a k)) do throw .invalidSignature
  return ()

end Libp2pAsm.Spec.Crypto.Curve25519.Ed25519
