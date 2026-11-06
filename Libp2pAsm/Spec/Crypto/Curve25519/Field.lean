import Libp2pAsm.Spec.Crypto.Basic

/-! Independent integer specification. Runtime code does not call these functions.
Equations and constants: RFC 7748 section 4.1; RFC 8032 sections 5.1 and 6. -/
namespace Libp2pAsm.Spec.Crypto.Curve25519

def prime : Nat := 2^255 - 19
def order : Nat := 2^252 + 27742317777372353535851937790883648493

def add (a b : Nat) : Nat := (a + b) % prime
def sub (a b : Nat) : Nat := (a % prime + prime - b % prime) % prime
def mul (a b : Nat) : Nat := a * b % prime

def power (a n : Nat) : Nat :=
  (List.range 256).foldl (fun acc i =>
    let squared := mul acc acc
    if n.testBit (255-i) then mul squared a else squared) 1

def inverse (a : Nat) : Nat := power a (prime-2)
def d : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555
def sqrtM1 : Nat := 19681161376707505956807079304988542015446066515923890162744021073123829784752

def decodeLE (bs : Bytes) : Nat := bs.foldr (fun b n => b.toNat + 256*n) 0
def encodeLE (n count : Nat) : Bytes :=
  (List.range count).map fun i => (n / 2^(8*i) % 256).toUInt8

def clamp (bs : Bytes) : Nat :=
  (decodeLE bs / 8 % 2^251) * 8 + 2^254

inductive Error where
  | invalidLength | zeroSharedSecret | noncanonical | invalidPoint | smallOrder | invalidSignature
  | messageTooLong
  deriving BEq, DecidableEq, Repr

end Libp2pAsm.Spec.Crypto.Curve25519
