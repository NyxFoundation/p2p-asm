import Libp2pAsm.Asm.Basic

/-!
RV64IM SHA-2 compression built solely from typed instructions and SAsm loops.
This module emits instructions; it does not execute the pure SHA specification.
See Tests/AsmCrypto/README.md for the memory contract and verification limits.
-/

namespace Libp2pAsm.Asm.Crypto.Sha2

open Rv64

inductive Variant where
  | sha256 | sha512
  deriving DecidableEq, BEq, Repr

def Variant.width : Variant → Nat | .sha256 => 32 | .sha512 => 64
def Variant.rounds : Variant → Nat | .sha256 => 64 | .sha512 => 80

/-- Working a..h occupy s0..s7; s8..s11 are never touched. -/
def working : List Reg := [.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23]

/-- All caller-saved registers except the preserved return address. -/
def cleared : List Reg :=
  [.x5, .x6, .x7, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
   .x28, .x29, .x30, .x31]

/-- a7 holds the low32 mask throughout SHA-256. -/
def normalize (v : Variant) (r : Reg) : List Instr :=
  match v with | .sha256 => [.AND r r .x17] | .sha512 => []

def add (v : Variant) (d a b : Reg) : List Instr :=
  [.ADD d a b] ++ normalize v d

/-- Source, destination and t2 must be distinct; SHA-256 source is canonical. -/
def rotate (v : Variant) (d a : Reg) (n : Nat) : List Instr :=
  [.SRLI d a (BitVec.ofNat 6 n),
   .SLLI .x7 a (BitVec.ofNat 6 (v.width - n)), .OR d d .x7] ++ normalize v d

/-- Destination is t1 or t4; source is t0, s0 or s4. Clobbers t2, t3. -/
def sigma (v : Variant) (d a : Reg) (r₁ r₂ r₃ : Nat) (small : Bool) : List Instr :=
  rotate v d a r₁ ++ rotate v .x28 a r₂ ++ [.XOR d d .x28] ++
  (if small then [.SRLI .x28 a (BitVec.ofNat 6 r₃)] else rotate v .x28 a r₃) ++
  [.XOR d d .x28]

def small0 (v : Variant) : List Instr :=
  match v with
  | .sha256 => sigma v .x29 .x5 7 18 3 true
  | .sha512 => sigma v .x29 .x5 1 8 7 true

def small1 (v : Variant) : List Instr :=
  match v with
  | .sha256 => sigma v .x6 .x5 17 19 10 true
  | .sha512 => sigma v .x6 .x5 19 61 6 true

def big0 (v : Variant) : List Instr :=
  match v with
  | .sha256 => sigma v .x29 .x8 2 13 22 false
  | .sha512 => sigma v .x29 .x8 28 34 39 false

def big1 (v : Variant) : List Instr :=
  match v with
  | .sha256 => sigma v .x6 .x20 6 11 25 false
  | .sha512 => sigma v .x6 .x20 14 18 41 false

private def enter (v : Variant) : SAsm.Stmt := .block <|
  [.ADDI .x2 .x2 (-64)] ++
  (working.zipIdx.flatMap fun (r, i) => [.SD .x2 r (BitVec.ofNat 12 (8*i))]) ++
  [.ADDI .x17 .x0 (-1)] ++
  (if v == .sha256 then [.SRLI .x17 .x17 32] else []) ++
  (working.zipIdx.flatMap fun (r, i) =>
    [.LD r .x10 (BitVec.ofNat 12 (8*i))] ++ normalize v r) ++
  [.ADDI .x14 .x12 0, .ADDI .x15 .x0 16]

/-- Fixed 4/8 byte loads per word allow every input alignment. -/
private def decodeWord (v : Variant) : SAsm.Stmt := .block <|
  [.ADDI .x5 .x0 0] ++
  ((List.range (v.width / 8)).flatMap fun i =>
    [.LBU .x6 .x11 (BitVec.ofNat 12 i), .SLLI .x5 .x5 8, .OR .x5 .x5 .x6]) ++
  [.SD .x12 .x5 0, .ADDI .x11 .x11 (BitVec.ofNat 12 (v.width / 8)),
   .ADDI .x12 .x12 8, .ADDI .x15 .x15 (-1)]

private def expandWord (v : Variant) : SAsm.Stmt := .block <|
  [.LD .x5 .x12 (-16)] ++ small1 v ++ [.LD .x5 .x12 (-120)] ++ small0 v ++
  add v .x6 .x6 .x29 ++ [.LD .x30 .x12 (-56)] ++ add v .x6 .x6 .x30 ++
  [.LD .x30 .x12 (-128)] ++ add v .x6 .x6 .x30 ++
  [.SD .x12 .x6 0, .ADDI .x12 .x12 8, .ADDI .x15 .x15 (-1)]

/-- Ch(e,f,g) = g XOR (e AND (f XOR g)). -/
def choose : List Instr :=
  [.XOR .x30 .x21 .x22, .AND .x30 .x20 .x30, .XOR .x30 .x30 .x22]

/-- Maj(a,b,c) = (a AND b) OR ((a OR b) AND c). -/
def majority : List Instr :=
  [.AND .x30 .x8 .x9, .OR .x31 .x8 .x9, .AND .x31 .x31 .x18,
   .OR .x30 .x30 .x31]

private def roundSums (v : Variant) : List Instr :=
  big1 v ++ choose ++ add v .x6 .x6 .x30 ++ add v .x6 .x6 .x23 ++
  [.LD .x30 .x13 0] ++ add v .x6 .x6 .x30 ++
  [.LD .x30 .x12 0] ++ add v .x6 .x6 .x30 ++
  big0 v ++ majority ++ add v .x29 .x29 .x30

private def roundStep (v : Variant) : SAsm.Stmt := .block <|
  roundSums v ++ [.ADDI .x23 .x22 0, .ADDI .x22 .x21 0, .ADDI .x21 .x20 0] ++
  add v .x20 .x19 .x6 ++ [.ADDI .x19 .x18 0, .ADDI .x18 .x9 0, .ADDI .x9 .x8 0] ++
  add v .x8 .x6 .x29 ++
  [.ADDI .x12 .x12 8, .ADDI .x13 .x13 8, .ADDI .x15 .x15 (-1)]

private def feedForward (v : Variant) : SAsm.Stmt := .block <|
  working.zipIdx.flatMap fun (r, i) =>
    [.LD .x5 .x10 (BitVec.ofNat 12 (8*i))] ++ normalize v .x5 ++
    add v r r .x5 ++ [.SD .x10 r (BitVec.ofNat 12 (8*i))]

private def wipe (v : Variant) : SAsm.Stmt := sequence [
  .block [.ADDI .x12 .x14 0, .ADDI .x15 .x0 (BitVec.ofNat 12 v.rounds)],
  .loop (.ne .x15 .x0) (.block
    [.SD .x12 .x0 0, .ADDI .x12 .x12 8, .ADDI .x15 .x15 (-1)])]

private def leave : SAsm.Stmt :=

  .block ((working.zipIdx.flatMap fun (r, i) =>
    [.LD r .x2 (BitVec.ofNat 12 (8*i)), .SD .x2 .x0 (BitVec.ofNat 12 (8*i))]) ++
    [.ADDI .x2 .x2 64] ++ (cleared.map fun r => .ADDI r .x0 0))

/-- Leaf ABI: a0=64-byte state, a1=block, a2=schedule, a3=immutable constants.
All except a1 are 8-byte aligned; sp is 16-byte aligned with 64 owned bytes below.
All regions are distinct, valid, nonwrapping, and disjoint from code. State and
schedule are writable; input/constants are readable. Constants must equal the
fixed SHA table in LE64 slots. SHA-256 accepts arbitrary high halves in state,
normalizes them, and returns canonical LE64 slots. Returns a0=0, preserves ra/sp,
gp/tp and all s-registers, clears other caller-saved registers and its stack frame.
-/
def compressBody (v : Variant) : SAsm.Stmt := sequence [
  enter v,
  .loop (.ne .x15 .x0) (decodeWord v),
  .block [.ADDI .x15 .x0 (BitVec.ofNat 12 (v.rounds - 16))],
  .loop (.ne .x15 .x0) (expandWord v),
  .block [.ADDI .x12 .x14 0, .ADDI .x15 .x0 (BitVec.ofNat 12 v.rounds)],
  .loop (.ne .x15 .x0) (roundStep v),
  feedForward v, wipe v, leave]

/-- Original standalone wrapper; factoring does not change any instruction. -/
def compress (v : Variant) : SAsm.Stmt := .seq (compressBody v) .ret

end Libp2pAsm.Asm.Crypto.Sha2
