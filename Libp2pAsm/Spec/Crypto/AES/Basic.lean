import Std

/-!
Independent byte-oriented AES-128 reference, following FIPS 197-upd1 sections
4 and 5: https://doi.org/10.6028/NIST.FIPS.197-upd1 . State is column-major.
The S-box uses field inversion and the affine transform, not the implementation
circuit. These pure definitions are specifications, never the assembly runtime.
-/
namespace Libp2pAsm.Spec.Crypto.AES

abbrev Byte := BitVec 8
abbrev Block := Vector UInt8 16
abbrev ExpandedKey := Vector UInt8 176

inductive Error where
  | invalidKeyLength | invalidBlockLength
  deriving DecidableEq, BEq, Repr

def xtime (x : Byte) : Byte :=
  (x <<< 1) ^^^ (if x.getLsbD 7 then 0x1b else 0)

def mul (x y : Byte) : Byte :=
  ((List.range 8).foldl (fun (a, b, z) _ =>
    (xtime a, b >>> 1, z ^^^ (if b.getLsbD 0 then a else 0))) (x, y, 0)).2.2

def power (x : Byte) (n : Nat) : Byte :=
  (List.range n).foldl (fun z _ => mul z x) 1

/-- Addition chain for x^254, including inverse(0) = 0. -/
def inverse (x : Byte) : Byte :=
  let x2 := mul x x
  let x3 := mul x2 x
  let x6 := mul x3 x3
  let x12 := mul x6 x6
  let x15 := mul x12 x3
  let x30 := mul x15 x15
  let x60 := mul x30 x30
  let x120 := mul x60 x60
  let x240 := mul x120 x120
  mul (mul x240 x12) x2

def subByte (x : Byte) : Byte :=
  let y := inverse x
  y ^^^ y.rotateLeft 1 ^^^ y.rotateLeft 2 ^^^ y.rotateLeft 3 ^^^ y.rotateLeft 4 ^^^ 0x63

def sbox (x : UInt8) : UInt8 := (subByte (BitVec.ofNat 8 x.toNat)).toNat.toUInt8

def rcon (i : Nat) : UInt8 :=
  ((List.range i).foldl (fun x _ => xtime x) 1).toNat.toUInt8

/-- Standard byte schedule; word i depends on i-1 and i-4. -/
def expand (key : Block) : ExpandedKey := Id.run do
  let mut bytes := key.toArray
  for i in List.range 40 do
    let word := i + 4
    let last := 4 * (word - 1)
    let temp := Vector.ofFn fun (j : Fin 4) =>
      if word % 4 == 0 then
        sbox bytes[last + (j.val + 1) % 4]! ^^^ (if j.val == 0 then rcon (word / 4 - 1) else 0)
      else bytes[last + j.val]!
    for j in List.range 4 do
      bytes := bytes.push (bytes[4 * (word - 4) + j]! ^^^ temp[j]!)
  return Vector.ofFn fun i => bytes[i.val]!

def addRoundKey (state : Block) (key : ExpandedKey) (round : Nat) : Block :=
  Vector.ofFn fun i => state[i] ^^^ key[16 * round + i.val]!

def subBytes (state : Block) : Block := state.map sbox

def shiftRows (state : Block) : Block :=
  Vector.ofFn fun i => state[4 * ((i.val / 4 + i.val % 4) % 4) + i.val % 4]!

def mixColumns (state : Block) : Block := Vector.ofFn fun i =>
  let byteAt := fun j => BitVec.ofNat 8 state[4 * (i.val / 4) + (i.val % 4 + j) % 4]!.toNat
  (mul 2 (byteAt 0) ^^^ mul 3 (byteAt 1) ^^^ byteAt 2 ^^^ byteAt 3).toNat.toUInt8

def encryptExpanded (key : ExpandedKey) (input : Block) : Block :=
  let initial := addRoundKey input key 0
  let state := (List.range 9).foldl (fun s r =>
    addRoundKey (mixColumns (shiftRows (subBytes s))) key (r + 1)) initial
  addRoundKey (shiftRows (subBytes state)) key 10

def encrypt (key input : Block) : Block := encryptExpanded (expand key) input

def encryptBytes (key input : Array UInt8) : Except Error (Array UInt8) := do
  if hk : key.size = 16 then
    if hi : input.size = 16 then return (encrypt ⟨key, hk⟩ ⟨input, hi⟩).toArray
    else throw .invalidBlockLength
  else throw .invalidKeyLength

/-- QUIC AES header protection uses the first five bytes of AES(sample). -/
def headerProtection (key sample : Block) : Vector UInt8 5 :=
  Vector.ofFn fun i => (encrypt key sample)[i.val]!

end Libp2pAsm.Spec.Crypto.AES
