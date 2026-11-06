import Libp2pAsm.Asm.Basic

namespace Libp2pAsm.Asm.Kernel
open Rv64
abbrev imm (n : Nat) : BitVec 12 := BitVec.ofNat 12 n
abbrev ins := SAsm.Stmt.block
abbrev seq := sequence
abbrev empty : SAsm.Stmt := ins []

def temps : List Reg := [.x5,.x6,.x7,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x28,.x29,.x30,.x31]
def saved : List Reg := [.x8,.x9,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x1]

def load (r : Reg) (n : Nat) : List Instr :=
  [.ADDI r .x0 (imm (n / 2^56 % 256))] ++
  (List.range 7).flatMap (fun i => [.SLLI r r 8, .ORI r r (imm (n / 2^(8*(6-i)) % 256))])

def li (r : Reg) (n : Nat) : SAsm.Stmt := ins (load r n)
def mov (r s : Reg) : SAsm.Stmt := ins [.ADDI r s 0]

def clear : List Instr := (temps.filter fun r => r != .x10 && r != .x11 && r != .x12).map
  (fun r => .ADDI r .x0 0)

def leave : SAsm.Stmt := seq [ins (
  (saved.zipIdx.map fun (r,i) => .LD r .x2 (imm (i*8))) ++
  ((List.range 32).map fun i => .SD .x2 .x0 (imm (i*8))) ++
  [.ADDI .x2 .x2 256] ++ clear), .ret]

def finish (status : Nat) : SAsm.Stmt := seq [
  ins [.ADDI .x10 .x0 (imm status), .ADDI .x11 .x0 0, .ADDI .x12 .x0 0],leave]
def reject (c : SAsm.Cond) (status : Nat) : SAsm.Stmt := .ite c (finish status) empty

def early (status : Nat) : SAsm.Stmt := seq [ins (
  [.ADDI .x10 .x0 (imm status), .ADDI .x11 .x0 0, .ADDI .x12 .x0 0] ++ clear),.ret]
def earlyReject (c : SAsm.Cond) (status : Nat) : SAsm.Stmt := .ite c (early status) empty

def span (p n : Reg) : SAsm.Stmt := seq [ins [.ADD .x5 p n],earlyReject (.ltu .x5 p) 9]
def apart (p n q m : Reg) : SAsm.Stmt := .ite (.ne n .x0) (.ite (.ne m .x0)
  (.ite (.ltu p q)
    (seq [ins [.SUB .x5 q p],earlyReject (.ltu .x5 n) 10])
    (seq [ins [.SUB .x5 p q],earlyReject (.ltu .x5 m) 10])) empty) empty

/-- Uniform ABI: state/cap, input/length, output/cap, option, budget.
All byte inputs may be unaligned. State/output are aligned; stack is 256 bytes.
The caller owns mapped regions and establishes code separation and structural state. -/
def enter (stateMin inputMin outputMin : Nat) : SAsm.Stmt := seq [
  span .x10 .x11,span .x12 .x13,span .x14 .x15,
  li .x7 stateMin,earlyReject (.ltu .x11 .x7) 11,
  li .x7 inputMin,earlyReject (.ltu .x13 .x7) 11,
  li .x7 outputMin,earlyReject (.ltu .x15 .x7) 11,
  ins [.OR .x5 .x10 .x14,.ANDI .x5 .x5 7],earlyReject (.ne .x5 .x0) 10,
  ins [.ANDI .x5 .x2 15],earlyReject (.ne .x5 .x0) 10,
  li .x7 256,earlyReject (.ltu .x2 .x7) 9,ins [.ADDI .x28 .x2 (-256)],
  apart .x10 .x11 .x12 .x13,apart .x10 .x11 .x14 .x15,
  apart .x12 .x13 .x14 .x15,apart .x28 .x7 .x10 .x11,
  apart .x28 .x7 .x12 .x13,apart .x28 .x7 .x14 .x15,
  ins ([.ADDI .x2 .x2 (-256)] ++ saved.zipIdx.map (fun (r,i) => .SD .x2 r (imm (i*8)))),
  ins [.ADDI .x8 .x10 0,.ADDI .x9 .x11 0,.ADDI .x18 .x12 0,.ADDI .x19 .x13 0,
    .ADDI .x20 .x14 0,.ADDI .x21 .x15 0,.ADDI .x22 .x16 0,.ADDI .x23 .x17 0]]

def readLE (dst ptr : Reg) (off : Nat) : SAsm.Stmt := ins <|
  [.ADDI dst .x0 0] ++ (List.range 8).reverse.flatMap (fun i =>
    [.SLLI dst dst 8,.LBU .x31 ptr (imm (off+i)),.OR dst dst .x31])
def input (r : Reg) (i : Nat) : SAsm.Stmt := readLE r .x18 (i*8)
def get (r : Reg) (i : Nat) : SAsm.Stmt := ins [.LD r .x8 (imm (i*8))]
def put (i : Nat) (r : Reg) : SAsm.Stmt := ins [.SD .x8 r (imm (i*8))]
def putN (i n : Nat) : SAsm.Stmt := seq [li .x7 n,put i .x7]
def success (a b : Reg) : SAsm.Stmt := seq [mov .x11 a,mov .x12 b,li .x10 0,leave]

def addChecked (dst a b : Reg) (err : Nat) : SAsm.Stmt := seq [
  ins [.ADD .x30 a b],reject (.ltu .x30 a) err,mov dst .x30]
def mulChecked (dst a b : Reg) (err : Nat) : SAsm.Stmt := seq [
  ins [.MULHU .x30 a b],reject (.ne .x30 .x0) err,ins [.MUL dst a b]]

end Libp2pAsm.Asm.Kernel
