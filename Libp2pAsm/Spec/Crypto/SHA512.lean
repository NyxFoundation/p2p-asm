import Libp2pAsm.Spec.Crypto.Basic

/-!
Independent transcription of FIPS 180-4 (August 2015), sections 4.1.3,
4.2.3, 5.1.2, 5.2.2, 5.3.5, and 6.4. No third-party implementation code
is adapted. Constants and equations are from the standard:
https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf
-/

namespace Libp2pAsm.Spec.Crypto.SHA512

abbrev State := Sha2.State 64
abbrev Block := Vector UInt8 128

def initial : State :=
  ⟨0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
   0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179⟩

def roundConstants : Vector (BitVec 64) 80 := #v[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

def bigSigma0 (x : BitVec 64) : BitVec 64 :=
  x.rotateRight 28 ^^^ x.rotateRight 34 ^^^ x.rotateRight 39

def bigSigma1 (x : BitVec 64) : BitVec 64 :=
  x.rotateRight 14 ^^^ x.rotateRight 18 ^^^ x.rotateRight 41

def smallSigma0 (x : BitVec 64) : BitVec 64 :=
  x.rotateRight 1 ^^^ x.rotateRight 8 ^^^ (x >>> 7)

def smallSigma1 (x : BitVec 64) : BitVec 64 :=
  x.rotateRight 19 ^^^ x.rotateRight 61 ^^^ (x >>> 6)

def blockWords (block : Block) : Vector (BitVec 64) 16 :=
  Vector.ofFn fun i =>
    Sha2.readWord 64 (Vector.ofFn (fun j : Fin 8 => block[8*i.val+j.val]'(by omega))).toList

private def extendSchedule (words : Vector (BitVec 64) 80)
    (i : Fin 64) : Vector (BitVec 64) 80 :=
  let t := i.val + 16
  let next := smallSigma1 words[t-2] + words[t-7] + smallSigma0 words[t-15] + words[t-16]
  words.set t next

def schedule (block : Block) : Vector (BitVec 64) 80 :=
  let first := blockWords block
  let words := Vector.ofFn fun i : Fin 80 => if h : i.val < 16 then first[i.val] else 0
  (List.finRange 64).foldl extendSchedule words

/-- One round, before the final feed-forward addition to the chaining state. -/
def round (s : State) (constant word : BitVec 64) : State :=
  let t1 := s.h + bigSigma1 s.e + Sha2.choose s.e s.f s.g + constant + word
  let t2 := bigSigma0 s.a + Sha2.majority s.a s.b s.c
  ⟨t1 + t2, s.a, s.b, s.c, s.d + t1, s.e, s.f, s.g⟩

/-- FIPS 180-4 section 6.4.2: 80 rounds followed by feed-forward. -/
def compress (state : State) (block : Block) : State :=
  let words := schedule block
  state.add ((List.finRange 80).foldl (fun s i => round s roundConstants[i.val] words[i.val]) state)

/-- Reject byte lengths >= 2^125. The full 128-bit bit length is encoded;
there is no artificial UInt64 restriction or wrap of the high length word. -/
def padding (byteLength : Nat) : Except Error Bytes := Sha2.padding 128 16 byteLength

/-- SHA-512 on byte-aligned messages, returning exactly 64 bytes on success. -/
def hash (message : List UInt8) : Except Error (List UInt8) := do
  let suffix ← padding message.length
  let state ← Sha2.foldBlocks 128 (by decide) compress initial (message ++ suffix)
  return state.toBytes

end Libp2pAsm.Spec.Crypto.SHA512
