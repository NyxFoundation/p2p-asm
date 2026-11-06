import Libp2pAsm.Spec.Crypto.Basic

/-!
Independent transcription of FIPS 180-4 (August 2015), sections 4.1.2,
4.2.2, 5.1.1, 5.2.1, 5.3.3, and 6.2. No third-party implementation code
is adapted. Constants and equations are from the standard:
https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf
-/

namespace Libp2pAsm.Spec.Crypto.SHA256

abbrev State := Sha2.State 32
abbrev Block := Vector UInt8 64

def initial : State :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
   0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

def roundConstants : Vector (BitVec 32) 64 := #v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def bigSigma0 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

def bigSigma1 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

def smallSigma0 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)

def smallSigma1 (x : BitVec 32) : BitVec 32 :=
  x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)

def blockWords (block : Block) : Vector (BitVec 32) 16 :=
  Vector.ofFn fun i =>
    Sha2.readWord 32 (Vector.ofFn (fun j : Fin 4 => block[4*i.val+j.val]'(by omega))).toList

private def extendSchedule (words : Vector (BitVec 32) 64)
    (i : Fin 48) : Vector (BitVec 32) 64 :=
  let t := i.val + 16
  let next := smallSigma1 words[t-2] + words[t-7] + smallSigma0 words[t-15] + words[t-16]
  words.set t next

def schedule (block : Block) : Vector (BitVec 32) 64 :=
  let first := blockWords block
  let words := Vector.ofFn fun i : Fin 64 => if h : i.val < 16 then first[i.val] else 0
  (List.finRange 48).foldl extendSchedule words

/-- One round, before the final feed-forward addition to the chaining state. -/
def round (s : State) (constant word : BitVec 32) : State :=
  let t1 := s.h + bigSigma1 s.e + Sha2.choose s.e s.f s.g + constant + word
  let t2 := bigSigma0 s.a + Sha2.majority s.a s.b s.c
  ⟨t1 + t2, s.a, s.b, s.c, s.d + t1, s.e, s.f, s.g⟩

/-- FIPS 180-4 section 6.2.2: 64 rounds followed by feed-forward. -/
def compress (state : State) (block : Block) : State :=
  let words := schedule block
  state.add ((List.finRange 64).foldl (fun s i => round s roundConstants[i.val] words[i.val]) state)

/-- Reject byte lengths >= 2^61; the 64-bit bit-length field never wraps. -/
def padding (byteLength : Nat) : Except Error Bytes := Sha2.padding 64 8 byteLength

/-- SHA-256 on byte-aligned messages, returning exactly 32 bytes on success. -/
def hash (message : List UInt8) : Except Error (List UInt8) := do
  let suffix ← padding message.length
  let state ← Sha2.foldBlocks 64 (by decide) compress initial (message ++ suffix)
  return state.toBytes

end Libp2pAsm.Spec.Crypto.SHA256
