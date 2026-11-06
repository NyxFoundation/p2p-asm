import Libp2pAsm.Spec.Crypto.AES.Basic

/-!
AES-128-GCM, 96-bit nonce and full 128-bit tag, SP 800-38D §§5.2, 6, 7.
https://doi.org/10.6028/NIST.SP.800-38D . Bytes and lengths use natural numbers;
validation precedes length arithmetic at the API. No runtime/side-channel claim.
-/
namespace Libp2pAsm.Spec.Crypto.GCM

abbrev Block := AES.Block
abbrev Nonce := Vector UInt8 12
abbrev Field := BitVec 128

inductive Error where
  | invalidKeyLength | invalidNonceLength | shortCiphertext
  | messageTooLong | aadTooLong | authenticationFailed
  | outputCapacity | workspaceCapacity
  deriving DecidableEq, BEq, Repr

/-- SP 800-38D: len(P) ≤ 2^39-256 bits, len(A) ≤ 2^64-1 bits. -/
def maxMessageBytes : Nat := 2^36 - 32
def maxAadBytes : Nat := 2^61 - 1

def validateLengths (nonceLength aadLength messageLength : Nat) : Except Error Unit := do
  if nonceLength != 12 then throw .invalidNonceLength
  if messageLength > maxMessageBytes then throw .messageTooLong
  if aadLength > maxAadBytes then throw .aadTooLong

/-- Check the short tag BEFORE subtraction, then output capacity. -/
def openLength (ciphertextLength capacity : Nat) : Except Error Nat := do
  if ciphertextLength < 16 then throw .shortCiphertext
  let n := ciphertextLength - 16
  if n > maxMessageBytes then throw .messageTooLong
  if capacity < n then throw .outputCapacity
  return n

def readBE (bytes : Array UInt8) : Field :=
  bytes.foldl (fun x b => (x <<< 8) ||| BitVec.ofNat 128 b.toNat) 0

def encodeBE (size value : Nat) : Array UInt8 :=
  (List.range size).toArray.map fun i => (value / 2^(8*(size-1-i)) % 256).toUInt8

def blockOf (bytes : Array UInt8) : Block := Vector.ofFn fun i => bytes[i.val]!

def fieldBytes (x : Field) : Block := blockOf (encodeBE 16 x.toNat)

/-- Algorithm 1, MSB first, with reduction R = 11100001 || 0^120. -/
def mul (x y : Field) : Field :=
  ((List.range 128).foldl (fun (z, v) i =>
    (z ^^^ (if x.getLsbD (127-i) then v else 0),
     (v >>> 1) ^^^ (if v.getLsbD 0 then 0xe1000000000000000000000000000000 else 0)))
    (0, y)).1

def hashPadded (h initial : Field) (bytes : Array UInt8) : Field :=
  (List.range ((bytes.size+15)/16)).foldl (fun acc i =>
    let chunk := Vector.ofFn fun (j : Fin 16) => bytes[16*i+j.val]?.getD 0
    mul (acc ^^^ readBE chunk.toArray) h) initial

def ghash (h : Field) (aad ciphertext : Array UInt8) : Field :=
  let y := hashPadded h (hashPadded h 0 aad) ciphertext
  let lengths := encodeBE 8 (aad.size*8) ++ encodeBE 8 (ciphertext.size*8)
  mul (y ^^^ readBE lengths) h

def j0 (nonce : Nonce) : Block := blockOf (nonce.toArray ++ #[0,0,0,1])

def counter (nonce : Nonce) (i : Nat) : Block :=
  blockOf (nonce.toArray ++ encodeBE 4 (i+2))

def ctr (key : AES.ExpandedKey) (nonce : Nonce) (input : Array UInt8) : Array UInt8 := Id.run do
  let mut output := #[]
  for i in List.range ((input.size+15)/16) do
    let stream := AES.encryptExpanded key (counter nonce i)
    for j in List.range (min 16 (input.size - 16*i)) do
      output := output.push (input[16*i+j]! ^^^ stream[j]!)
  return output

def tag (key : AES.ExpandedKey) (nonce : Nonce) (aad ciphertext : Array UInt8) : Block :=
  let h := readBE (AES.encryptExpanded key (Vector.replicate 16 0)).toArray
  let s := ghash h aad ciphertext
  let mask := readBE (AES.encryptExpanded key (j0 nonce)).toArray
  fieldBytes (s ^^^ mask)

def «seal» (key nonce aad plaintext : Array UInt8) : Except Error (Array UInt8) := do
  if hk : key.size = 16 then
    validateLengths nonce.size aad.size plaintext.size
    if hn : nonce.size = 12 then
      let expanded := AES.expand ⟨key, hk⟩
      let ciphertext := ctr expanded ⟨nonce, hn⟩ plaintext
      return ciphertext ++ (tag expanded ⟨nonce, hn⟩ aad ciphertext).toArray
    else throw .invalidNonceLength
  else throw .invalidKeyLength

def «open» (key nonce aad sealed : Array UInt8) : Except Error (Array UInt8) := do
  if hk : key.size = 16 then
    if nonce.size != 12 then throw .invalidNonceLength
    let n ← openLength sealed.size sealed.size
    validateLengths nonce.size aad.size n
    if hn : nonce.size = 12 then
      let expanded := AES.expand ⟨key, hk⟩
      let ciphertext := sealed.extract 0 n
      let expected := (tag expanded ⟨nonce, hn⟩ aad ciphertext).toArray
      if expected != sealed.extract n sealed.size then throw .authenticationFailed
      return ctr expanded ⟨nonce, hn⟩ ciphertext
    else throw .invalidNonceLength
  else throw .invalidKeyLength

end Libp2pAsm.Spec.Crypto.GCM
