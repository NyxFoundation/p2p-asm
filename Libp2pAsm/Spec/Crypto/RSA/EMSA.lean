import Libp2pAsm.Spec.Crypto.RSA.Basic

/-! RFC 8017 §§9.1.2, 9.2, B.2.1 and RFC 8446 §4.2.3.
SHA256, MGF1-SHA256, salt length 32, trailer 0xbc only. -/
namespace Libp2pAsm.Spec.Crypto.RSA

def digestInfo : List UInt8 :=
  [0x30,0x31,0x30,0x0d,0x06,0x09,0x60,0x86,0x48,0x01,
   0x65,0x03,0x04,0x02,0x01,0x05,0x00,0x04,0x20]

def pkcsEncode (k : Nat) (digest : List UInt8) : Option (List UInt8) :=
  if digest.length == 32 && k ≥ 62 then
    some ([0,1] ++ List.replicate (k-54) 0xff ++ [0] ++ digestInfo ++ digest)
  else none

def pkcsVerify (digest em : List UInt8) : Bool :=
  pkcsEncode em.length digest == some em

def mgf1 (seed : List UInt8) (size : Nat) : Option (List UInt8) := do
  if size > 32*2^32 then none else do
    let blocks ← (List.range ((size+31)/32)).mapM fun counter =>
      (SHA256.hash (seed ++ i2osp 4 counter)).toOption
    pure (blocks.flatten.take size)

def pssVerify (bits : Nat) (digest em : List UInt8) : Bool := Id.run do
  let len := (bits+7)/8
  if digest.length != 32 || bits == 0 || em.length != len || len < 66 then return false
  let dbLen := len-33
  let masked := em.take dbLen
  let h := (em.drop dbLen).take 32
  if em.getLast? != some 0xbc || masked.head!.toNat ≥ 2^(8*len-bits |> fun u => 8-u) then
    return false
  let some mask := mgf1 h dbLen | return false
  let db := (masked.zip mask).map fun (a,b) => a ^^^ b
  let db := (db.head! &&& (255 / 2^(8*len-bits)).toUInt8) :: db.tail
  if db.take (dbLen-32) != List.replicate (dbLen-33) 0 ++ [1] then return false
  let .ok expected := SHA256.hash (List.replicate 8 0 ++ digest ++ db.drop (dbLen-32))
    | return false
  return h == expected

inductive Scheme where | pkcs1Sha256 | pssRsaeSha256
  deriving BEq, Repr

/-- PKCS1 is for certificate signatures only; TLS CertificateVerify uses PSS.
The main-owned DER/TLS layer enforces key OID and signature-scheme context. -/
def verify (scheme : Scheme) (minimumBits : Nat) (nb eb digest sig : List UInt8) : Bool :=
  if !tlsPolicy minimumBits nb || digest.length != 32 then false else
  match rsavp1 nb eb sig with
  | none => false
  | some m => match scheme with
    | .pkcs1Sha256 => pkcsVerify digest (i2osp nb.length m)
    | .pssRsaeSha256 =>
      let bits := bitLength (os2ip nb)-1
      let len := (bits+7)/8
      m < 256^len && pssVerify bits digest (i2osp len m)

end Libp2pAsm.Spec.Crypto.RSA
