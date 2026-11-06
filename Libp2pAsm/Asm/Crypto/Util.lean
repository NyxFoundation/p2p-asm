import Libp2pAsm.Asm.Crypto.Sha2

namespace Libp2pAsm.Asm.Crypto.Util
open Rv64

abbrev imm (n : Nat) : BitVec 12 := BitVec.ofNat 12 n
abbrev block := SAsm.Stmt.block
abbrev empty : SAsm.Stmt := .block []

/-- Generation-time expansion into ordinary RV64 instructions, no runtime oracle. -/
def load (r : Reg) (n : Nat) : List Instr :=
  [.ADDI r .x0 (imm (n / 2^56 % 256))] ++
  ((List.range 7).flatMap fun i =>
    [.SLLI r r 8, .ORI r r (imm (n / 2^(8*(6-i)) % 256))])

def saved : List Reg := [.x8, .x9, .x18, .x19, .x20, .x21,
  .x22, .x23, .x24, .x25, .x26, .x27, .x1]

/-- 112-byte frame. All 104 saved bytes and 8 padding bytes are wiped on exit. -/
def enter : SAsm.Stmt := block <|
  [.ADDI .x2 .x2 (-112)] ++
  (saved.zipIdx.map fun (r, i) => .SD .x2 r (imm (i*8)))

def clearTemps : List Instr :=
  (Sha2.cleared.filter (· != .x10)).map fun r => .ADDI r .x0 0

def leave : SAsm.Stmt := sequence [block <|
  (saved.zipIdx.flatMap fun (r, i) =>
    [.LD r .x2 (imm (8*i)), .SD .x2 .x0 (imm (8*i))]) ++
  [.SD .x2 .x0 104, .ADDI .x2 .x2 112] ++ clearTemps, .ret]

def finish (status : Nat := 0) : SAsm.Stmt := sequence [
  block ([.ADDI .x10 .x0 (imm status)] ++ clearTemps), .ret]

def reject (c : SAsm.Cond) (status : Nat) : SAsm.Stmt := .ite c (finish status) empty

/-- Check the last accessed byte, allowing a valid range ending at 2^64.
Clobbers t0/t1. An empty range never inspects the pointer or dereferences it. -/
def range (ptr len : Reg) : SAsm.Stmt := .ite (.ne len .x0) (sequence [
  block [.ADDI .x5 .x0 (-1), .SUB .x5 .x5 ptr, .ADDI .x6 len (-1)],
  reject (.ltu .x5 .x6) 4]) empty

def capacity (cap : Reg) (size : Nat) : SAsm.Stmt := sequence [
  block (load .x7 size), reject (.ltu cap .x7) 5]

/-- a checked byte loop; arguments are distinct from t0/t1/t2. -/
def copy (dst src count : Reg) : SAsm.Stmt := sequence [
  block [.ADDI .x5 dst 0, .ADDI .x6 src 0, .ADDI .x7 count 0],
  .loop (.ne .x7 .x0) (block [.LBU .x28 .x6 0, .SB .x5 .x28 0,
    .ADDI .x5 .x5 1, .ADDI .x6 .x6 1, .ADDI .x7 .x7 (-1)])]

/-- Wipe exactly count bytes; no alignment requirement. -/
def wipe (ptr count : Reg) : SAsm.Stmt := sequence [
  block [.ADDI .x5 ptr 0, .ADDI .x6 count 0],
  .loop (.ne .x6 .x0) (block [.SB .x5 .x0 0,
    .ADDI .x5 .x5 1, .ADDI .x6 .x6 (-1)])]

def storeBE (dst src : Reg) (offset bytes : Nat) : List Instr :=
  (List.range bytes).flatMap fun i =>
    [.SRLI .x7 src (BitVec.ofNat 6 (8*(bytes-1-i))), .SB dst .x7 (imm (offset+i))]

end Libp2pAsm.Asm.Crypto.Util
