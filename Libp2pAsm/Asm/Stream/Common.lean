import Libp2pAsm.Asm.Crypto.Link

namespace Libp2pAsm.Asm.Stream
open Rv64 Crypto.Util

abbrev seq := sequence
abbrev b := SAsm.Stmt.block
abbrev nil : SAsm.Stmt := .block []

def saves : List Reg := Crypto.Util.saved ++ [.x26, .x27]

def enter : SAsm.Stmt := b <| [.ADDI .x2 .x2 (-128)] ++
  (saves.zipIdx.map fun (r,i) => .SD .x2 r (imm (8*i)))

def temps : List Reg := [.x5,.x6,.x7,.x15,.x16,.x17,.x28,.x29,.x30,.x31]

def exit (stack : Bool) : SAsm.Stmt := seq [b <|
  (if stack then (saves.zipIdx.flatMap fun (r,i) =>
    [.LD r .x2 (imm (8*i)), .SD .x2 .x0 (imm (8*i))]) ++
    [.SD .x2 .x0 120, .ADDI .x2 .x2 128] else []) ++
  (temps.map fun r => .ADDI r .x0 0), .ret]

def fail (status : Nat) (stack : Bool := true) : SAsm.Stmt := seq [
  b [.ADDI .x10 .x0 (imm status), .ADDI .x11 .x0 0, .ADDI .x12 .x0 0,
    .ADDI .x13 .x0 0, .ADDI .x14 .x0 0], exit stack]

def guard (c : SAsm.Cond) (status : Nat := 1) (stack : Bool := true) : SAsm.Stmt :=
  .ite c (fail status stack) nil

/-- Reject wrapping capacity before dereferencing. Zero capacity permits any base. -/
def span (ptr len : Reg) (stack : Bool := true) : SAsm.Stmt := .ite (.ne len .x0) (seq [
  b [.ADDI .x5 .x0 (-1), .SUB .x5 .x5 ptr, .ADDI .x6 len (-1)],
  guard (.ltu .x5 .x6) 1 stack]) nil

def preflight (size : Nat) : SAsm.Stmt := seq [
  b [.ANDI .x5 .x10 7, .ADDI .x6 .x0 (imm size)],
  guard (.ne .x5 .x0) 1 false, guard (.ltu .x11 .x6) 1 false,
  span .x10 .x11 false, enter, b [.ADDI .x8 .x10 0]]

/-- a2=registered source base, a3=capacity, a4=view offset, a5=view length.
Returns resolved pointer in a2; does not derive an address from frame offset. -/
def sourceView : SAsm.Stmt := seq [
  guard (.ltu .x13 .x15), b [.SUB .x5 .x13 .x15],
  guard (.ltu .x5 .x14), span .x12 .x13,
  b [.ADD .x12 .x12 .x14]]

def zeroOutputs : SAsm.Stmt := b [.ADDI .x10 .x0 0, .ADDI .x11 .x0 0,
  .ADDI .x12 .x0 0, .ADDI .x13 .x0 0, .ADDI .x14 .x0 0]

end Libp2pAsm.Asm.Stream
