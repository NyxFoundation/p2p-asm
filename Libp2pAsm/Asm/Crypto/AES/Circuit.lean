import Libp2pAsm.Asm.Basic

/-!
Boyar–Peralta S-box circuit translated from BearSSL aes_ct64.c, commit
7561e7d6c86171257a4153d95202b0791b3612a8, blob 981e63d9ae459eb283c3db357a6bc25a2200c4df.
Copyright (c) 2016 Thomas Pornin <pornin@bolet.org>. MIT: LICENSES/bearssl.txt.
Primary: https://www.bearssl.org/gitweb/?p=BearSSL;a=blob_plain;f=src/symcipher/aes_ct64.c;hb=7561e7d6c86171257a4153d95202b0791b3612a8
Retrieved identical commit via https://github.com/ryanwoodsmall/bearssl-mirror .
Circuit paper: https://eprint.iacr.org/2009/191 . Inputs/outputs below are LSB
first, reversing BearSSL's x0..x7 / s0..s7. Only the S-box circuit is reused.
The circuit description is compiled to real LD/XOR/AND/XORI/SD instructions;
its evaluator is for refinement/testing, not the cryptographic runtime.
-/
namespace Libp2pAsm.Asm.Crypto.AES.Circuit
open Rv64

inductive Op where
  | xor | and
  deriving DecidableEq, BEq, Repr

structure Gate where
  dst : Nat
  left : Nat
  right : Nat
  op : Op
  invertRight : Bool
  deriving DecidableEq, BEq, Repr

def gates : List Gate := [
  ⟨8, 4, 2, .xor, false⟩,
  ⟨9, 7, 1, .xor, false⟩,
  ⟨10, 7, 4, .xor, false⟩,
  ⟨11, 7, 2, .xor, false⟩,
  ⟨12, 6, 5, .xor, false⟩,
  ⟨13, 12, 0, .xor, false⟩,
  ⟨14, 13, 4, .xor, false⟩,
  ⟨15, 9, 8, .xor, false⟩,
  ⟨16, 13, 7, .xor, false⟩,
  ⟨17, 13, 1, .xor, false⟩,
  ⟨18, 17, 11, .xor, false⟩,
  ⟨19, 3, 15, .xor, false⟩,
  ⟨20, 19, 2, .xor, false⟩,
  ⟨21, 19, 6, .xor, false⟩,
  ⟨22, 20, 0, .xor, false⟩,
  ⟨23, 20, 12, .xor, false⟩,
  ⟨24, 21, 10, .xor, false⟩,
  ⟨25, 0, 24, .xor, false⟩,
  ⟨26, 23, 24, .xor, false⟩,
  ⟨27, 23, 11, .xor, false⟩,
  ⟨28, 12, 24, .xor, false⟩,
  ⟨29, 9, 28, .xor, false⟩,
  ⟨30, 7, 28, .xor, false⟩,
  ⟨31, 15, 20, .and, false⟩,
  ⟨32, 18, 22, .and, false⟩,
  ⟨33, 32, 31, .xor, false⟩,
  ⟨34, 14, 0, .and, false⟩,
  ⟨35, 34, 31, .xor, false⟩,
  ⟨36, 9, 28, .and, false⟩,
  ⟨37, 17, 13, .and, false⟩,
  ⟨38, 37, 36, .xor, false⟩,
  ⟨39, 16, 25, .and, false⟩,
  ⟨40, 39, 36, .xor, false⟩,
  ⟨41, 10, 24, .and, false⟩,
  ⟨42, 8, 26, .and, false⟩,
  ⟨43, 42, 41, .xor, false⟩,
  ⟨44, 11, 23, .and, false⟩,
  ⟨45, 44, 41, .xor, false⟩,
  ⟨46, 33, 43, .xor, false⟩,
  ⟨47, 35, 45, .xor, false⟩,
  ⟨48, 38, 43, .xor, false⟩,
  ⟨49, 40, 45, .xor, false⟩,
  ⟨50, 46, 21, .xor, false⟩,
  ⟨51, 47, 27, .xor, false⟩,
  ⟨52, 48, 29, .xor, false⟩,
  ⟨53, 49, 30, .xor, false⟩,
  ⟨54, 50, 51, .xor, false⟩,
  ⟨55, 50, 52, .and, false⟩,
  ⟨56, 53, 55, .xor, false⟩,
  ⟨57, 54, 56, .and, false⟩,
  ⟨58, 57, 51, .xor, false⟩,
  ⟨59, 52, 53, .xor, false⟩,
  ⟨60, 51, 55, .xor, false⟩,
  ⟨61, 60, 59, .and, false⟩,
  ⟨62, 61, 53, .xor, false⟩,
  ⟨63, 52, 62, .xor, false⟩,
  ⟨64, 56, 62, .xor, false⟩,
  ⟨65, 53, 64, .and, false⟩,
  ⟨66, 65, 63, .xor, false⟩,
  ⟨67, 56, 65, .xor, false⟩,
  ⟨68, 58, 67, .and, false⟩,
  ⟨69, 54, 68, .xor, false⟩,
  ⟨70, 69, 66, .xor, false⟩,
  ⟨71, 58, 62, .xor, false⟩,
  ⟨72, 58, 69, .xor, false⟩,
  ⟨73, 62, 66, .xor, false⟩,
  ⟨74, 71, 70, .xor, false⟩,
  ⟨75, 73, 20, .and, false⟩,
  ⟨76, 66, 22, .and, false⟩,
  ⟨77, 62, 0, .and, false⟩,
  ⟨78, 72, 28, .and, false⟩,
  ⟨79, 69, 13, .and, false⟩,
  ⟨80, 58, 25, .and, false⟩,
  ⟨81, 71, 24, .and, false⟩,
  ⟨82, 74, 26, .and, false⟩,
  ⟨83, 70, 23, .and, false⟩,
  ⟨84, 73, 15, .and, false⟩,
  ⟨85, 66, 18, .and, false⟩,
  ⟨86, 62, 14, .and, false⟩,
  ⟨87, 72, 9, .and, false⟩,
  ⟨88, 69, 17, .and, false⟩,
  ⟨89, 58, 16, .and, false⟩,
  ⟨90, 71, 10, .and, false⟩,
  ⟨91, 74, 8, .and, false⟩,
  ⟨92, 70, 11, .and, false⟩,
  ⟨93, 90, 91, .xor, false⟩,
  ⟨94, 85, 86, .xor, false⟩,
  ⟨95, 80, 88, .xor, false⟩,
  ⟨96, 84, 85, .xor, false⟩,
  ⟨97, 77, 87, .xor, false⟩,
  ⟨98, 77, 80, .xor, false⟩,
  ⟨99, 82, 83, .xor, false⟩,
  ⟨100, 75, 78, .xor, false⟩,
  ⟨101, 81, 82, .xor, false⟩,
  ⟨102, 91, 92, .xor, false⟩,
  ⟨103, 87, 95, .xor, false⟩,
  ⟨104, 97, 100, .xor, false⟩,
  ⟨105, 79, 93, .xor, false⟩,
  ⟨106, 78, 101, .xor, false⟩,
  ⟨107, 93, 104, .xor, false⟩,
  ⟨108, 89, 104, .xor, false⟩,
  ⟨109, 99, 105, .xor, false⟩,
  ⟨110, 96, 105, .xor, false⟩,
  ⟨111, 79, 106, .xor, false⟩,
  ⟨112, 108, 109, .xor, false⟩,
  ⟨113, 76, 110, .xor, false⟩,
  ⟨114, 106, 110, .xor, false⟩,
  ⟨115, 103, 109, .xor, true⟩,
  ⟨116, 95, 107, .xor, true⟩,
  ⟨117, 111, 112, .xor, false⟩,
  ⟨118, 100, 113, .xor, false⟩,
  ⟨119, 98, 113, .xor, false⟩,
  ⟨120, 94, 112, .xor, false⟩,
  ⟨121, 111, 118, .xor, true⟩,
  ⟨122, 102, 117, .xor, true⟩]

def outputs : List Nat := [116, 115, 120, 119, 118, 122, 121, 114]

def scratchBytes : Nat := 984

/-- Every wire has a dedicated static LE64 slot; x12 is the aligned base.
Clobbers only x5,x6. All slots fit positive signed 12-bit immediates. -/
def compileGate (g : Gate) : List Instr :=
  [.LD .x5 .x12 (BitVec.ofNat 12 (8*g.left)),
   .LD .x6 .x12 (BitVec.ofNat 12 (8*g.right))] ++
  (if g.invertRight then [.XORI .x6 .x6 (-1)] else []) ++
  [match g.op with | .xor => .XOR .x5 .x5 .x6 | .and => .AND .x5 .x5 .x6,
   .SD .x12 .x5 (BitVec.ofNat 12 (8*g.dst))]

def code : SAsm.Stmt := .block (gates.flatMap compileGate)

def evaluate (input : BitVec 8) : BitVec 8 :=
  let initial := (List.range 8).toArray.map fun i => input.getLsbD i
  let wires := gates.foldl (fun wires g =>
    let a := wires[g.left]!
    let b := wires[g.right]! != g.invertRight
    wires.push (match g.op with | .xor => a != b | .and => a && b)) initial
  BitVec.ofNat 8 ((outputs.zipIdx).foldl (fun n (w, i) =>
    n + if wires[w]! then 2^i else 0) 0)

end Libp2pAsm.Asm.Crypto.AES.Circuit
