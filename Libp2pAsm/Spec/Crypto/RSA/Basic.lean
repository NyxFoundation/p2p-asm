import Libp2pAsm.Spec.Crypto.SHA256

/-! Independent unbounded-integer specification of RFC 8017 §§4, 5.2.2.
No machine arithmetic or assembly implementation is imported. -/
namespace Libp2pAsm.Spec.Crypto.RSA

def os2ip : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat * 256^bs.length + os2ip bs

def i2osp (width n : Nat) : List UInt8 :=
  (List.range width).map fun i => (n / 256^(width-1-i) % 256).toUInt8

def minimal (bs : List UInt8) : Bool :=
  match bs with | [] => false | b :: _ => b != 0

def bitLength (n : Nat) : Nat := if n == 0 then 0 else n.log2 + 1

/-- Unbounded square-and-multiply; termination follows exponent division. -/
def modexp (a e n : Nat) : Nat :=
  if e = 0 then 1 % n else
    let h := modexp a (e/2) n
    (h*h*(if e%2 == 0 then 1 else a)) % n
termination_by e
decreasing_by omega

def validKey (nb eb : List UInt8) : Bool :=
  let n := os2ip nb
  let e := os2ip eb
  minimal nb && minimal eb && n ≥ 5 && n%2 == 1 && e ≥ 3 && e%2 == 1 && e < n

/-- Local TLS strength policy, distinct from mathematical key validity. -/
def tlsPolicy (minimumBits : Nat) (nb : List UInt8) : Bool :=
  minimumBits ≥ 2048 && bitLength (os2ip nb) ≥ minimumBits

def rsavp1 (nb eb sig : List UInt8) : Option Nat :=
  if validKey nb eb && sig.length == nb.length && os2ip sig < os2ip nb then
    some (modexp (os2ip sig) (os2ip eb) (os2ip nb)) else none

end Libp2pAsm.Spec.Crypto.RSA
