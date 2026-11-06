import Libp2pAsm.Asm.Tls.Common

namespace Libp2pAsm.Asm.Quic.Recovery
open Rv64 Crypto.Util

/-! This is a generation-time arithmetic notation, not a runtime interpreter.
Every expression expands to ordinary typed RV64IM instructions. Seven temporary
registers bound expression depth. x11=work, x12=event, x13=staged action,
x14=packet, x15=path, x16=space. All other ABI registers remain untouched. -/
inductive E where
  | n (v : Nat)
  | mem (base : Reg) (word : Nat)
  | reg (r : Reg)
  | add (a b : E) | sub (a b : E) | mul (a b : E) | div (a b : E)
  | band (a b : E) | shr (a b : E)
  deriving Inhabited

def regs : Array Reg := #[.x5,.x6,.x7,.x28,.x29,.x30,.x31]
def constant (r : Reg) (n : Nat) : List Instr :=
  if n < 2048 then [.ADDI r .x0 (imm n)] else load r n
def E.emit (e : E) (depth : Nat := 0) : List Instr :=
  let r := regs[depth]?.getD .x31
  let t := regs[depth+1]?.getD .x31
  match e with
  | .n value => constant r value
  | .mem base w => [.LD r base (imm (8*w))]
  | .reg src => [.ADDI r src 0]
  | .add a b => a.emit depth ++ b.emit (depth+1) ++ [.ADD r r t]
  | .sub a b => a.emit depth ++ b.emit (depth+1) ++ [.SUB r r t]
  | .mul a b => a.emit depth ++ b.emit (depth+1) ++ [.MUL r r t]
  | .div a b => a.emit depth ++ b.emit (depth+1) ++ [.DIVU r r t]
  | .band a b => a.emit depth ++ b.emit (depth+1) ++ [.AND r r t]
  | .shr a b => a.emit depth ++ b.emit (depth+1) ++ [.SRL r r t]

abbrev h (w : Nat) : E := .mem .x11 w
abbrev e (w : Nat) : E := .mem .x12 w
abbrev p (w : Nat) : E := .mem .x14 w
abbrev q (w : Nat) : E := .mem .x15 w
abbrev z (w : Nat) : E := .mem .x16 w
abbrev n := E.n
abbrev add := E.add
abbrev sub := E.sub
abbrev mul := E.mul
abbrev div := E.div
def put (base : Reg) (w : Nat) (v : E) : SAsm.Stmt := block (v.emit ++ [.SD base .x5 (imm (8*w))])
def H := put .x11
def P := put .x14
def Q := put .x15
def Z := put .x16
def O := put .x13
def set (r : Reg) (v : E) : SAsm.Stmt := block (v.emit ++ [.ADDI r .x5 0])

def carryInstructions : List Instr := [.ADD .x28 .x5 .x6, .SLTU .x29 .x28 .x5]

/-- Inverted short branch followed by a long JAL supports large generated arms. -/
def when (c : SAsm.Cond) (body : SAsm.Stmt) : SAsm.Stmt := .ite c.neg empty body
def eq (a b : E) (body : SAsm.Stmt) : SAsm.Stmt :=
  sequence [block (a.emit ++ b.emit 1), when (.eq .x5 .x6) body]
def ne (a b : E) (body : SAsm.Stmt) : SAsm.Stmt :=
  sequence [block (a.emit ++ b.emit 1), when (.ne .x5 .x6) body]
def lt (a b : E) (body : SAsm.Stmt) : SAsm.Stmt :=
  sequence [block (a.emit ++ b.emit 1), when (.ltu .x5 .x6) body]
def le (a b : E) (body : SAsm.Stmt) : SAsm.Stmt :=
  sequence [block (b.emit ++ a.emit 1), when (.geu .x5 .x6) body]

/-- Internal error exit wipes exactly the validated work span. No stack is used. -/
def done (status : Nat) : SAsm.Stmt := sequence [
  block [.LD .x5 .x10 48, .LD .x6 .x10 8, .SRLI .x6 .x6 3, .ADDI .x6 .x6 8],
  .loop (.ne .x6 .x0) (block [.SD .x5 .x0 0, .ADDI .x5 .x5 8, .ADDI .x6 .x6 (-1)]),
  finish status]

def copyWords : SAsm.Stmt := sequence [
  block [.ADDI .x5 .x14 0, .ADDI .x6 .x15 0, .SRLI .x7 .x16 3],
  .loop (.ne .x7 .x0) (block [.LD .x28 .x6 0, .SD .x5 .x28 0,
    .ADDI .x5 .x5 8, .ADDI .x6 .x6 8, .ADDI .x7 .x7 (-1)])]

def commit : SAsm.Stmt := sequence [
  block [.LD .x14 .x10 0, .LD .x15 .x10 48, .LD .x16 .x10 8], copyWords,
  block [.LD .x14 .x10 32, .ADD .x15 .x15 .x16, .ADDI .x16 .x0 64], copyWords,
  done 0]
def needEq (a b : E) (status : Nat) : SAsm.Stmt := ne a b (done status)
def needLt (a b : E) (status : Nat) : SAsm.Stmt := le b a (done status)
def needLe (a b : E) (status : Nat) : SAsm.Stmt := lt b a (done status)
def nonzero (a : E) (status : Nat) : SAsm.Stmt := eq a (n 0) (done status)
def flag (a : E) : SAsm.Stmt := needLe a (n 1) 2

def checkedAdd (base : Reg) (w : Nat) (a b : E) : SAsm.Stmt := sequence [
  block (a.emit ++ b.emit 1 ++ [.ADD .x7 .x5 .x6]),
  when (.ltu .x7 .x5) (done 3), block [.SD base .x7 (imm (8*w))]]

/-- Exact unsigned 128/64 division. The quotient must fit a word. MULHU catches
the product's high half; the 64 fixed iterations handle the shifted carry before
subtraction. No 64-bit intermediate is silently treated as an integer product. -/
def mulDiv (a b denominator : E) (ceil : Bool) : SAsm.Stmt := sequence [
  block (a.emit ++ b.emit 1 ++ denominator.emit 2 ++
    [.MULHU .x28 .x5 .x6, .MUL .x5 .x5 .x6, .ADDI .x6 .x28 0]),
  when (.eq .x7 .x0) (done 10), when (.geu .x6 .x7) (done 3),
  block [.ADDI .x28 .x0 64, .ADDI .x29 .x0 0],
  .loop (.ne .x28 .x0) (sequence [
    block [.SRLI .x30 .x6 63, .SRLI .x31 .x5 63, .SLLI .x6 .x6 1,
      .OR .x6 .x6 .x31, .SLLI .x5 .x5 1, .SLLI .x29 .x29 1],
    .ite (.ne .x30 .x0)
      (block [.SUB .x6 .x6 .x7, .ORI .x29 .x29 1])
      (.ite (.geu .x6 .x7) (block [.SUB .x6 .x6 .x7, .ORI .x29 .x29 1]) empty),
    block [.ADDI .x28 .x28 (-1)]]),
  if ceil then when (.ne .x6 .x0) (sequence [
    block [.ADDI .x29 .x29 1], when (.eq .x29 .x0) (done 3)]) else empty,
  block [.ADDI .x5 .x29 0]]

def saveMulDiv (base : Reg) (w : Nat) (a b d : E) (ceil := false) : SAsm.Stmt :=
  sequence [mulDiv a b d ceil, block [.SD base .x5 (imm (8*w))]]

def maximum (base : Reg) (w : Nat) (a b : E) : SAsm.Stmt := sequence [
  block (a.emit ++ b.emit 1), .ite (.ltu .x5 .x6) (block [.ADDI .x5 .x6 0]) empty,
  block [.SD base .x5 (imm (8*w))]]
def minimum (base : Reg) (w : Nat) (a b : E) : SAsm.Stmt := sequence [
  block (a.emit ++ b.emit 1), .ite (.ltu .x6 .x5) (block [.ADDI .x5 .x6 0]) empty,
  block [.SD base .x5 (imm (8*w))]]

def pathAt (index : E) : SAsm.Stmt :=
  set .x15 (add (.reg .x11) (add (n 512) (mul index (n 256))))
def packetAt (index : E) : SAsm.Stmt :=
  set .x14 (add (.reg .x11) (add (add (n 512) (mul (h 4) (n 256))) (mul index (n 160))))
def spaceAt (index : E) : SAsm.Stmt :=
  set .x16 (add (.reg .x11) (add (n 256) (mul index (n 64))))
def rangesBase : E := add (.reg .x11) (add (add (n 512) (mul (h 4) (n 256))) (mul (h 3) (n 160)))

def selectPath (index : E) : SAsm.Stmt := sequence [needLt index (h 4) 2, pathAt index,
  needEq (q 0) (n 1) 10, needEq (q 23) (n 0) 10]
def selectSpace (index : E) : SAsm.Stmt := sequence [needLt index (n 3) 2, spaceAt index,
  needEq (z 1) (n 0) 10, needEq (.band (.shr (h 31) index) (n 1)) (n 1) 10]
def selectPacket (index : E) : SAsm.Stmt := sequence [needLt index (h 12) 6, packetAt index,
  pathAt (p 2), needEq (q 0) (n 1) 10, spaceAt (p 1)]
def ready : SAsm.Stmt := sequence [needEq (h 63) (n 0) 13, needEq (h 23) (n 0) 11,
  needLe (h 16) (e 2) 2]
def generation : SAsm.Stmt := needEq (e 1) (h 1) 6
def packetAction (kind : Nat) (index : E) : SAsm.Stmt := sequence [
  O 0 (n kind), O 1 index, O 2 (p 3), O 3 (p 11), O 4 (p 14),
  O 5 (p 7), O 6 (p 8), O 7 (p 9)]

end Libp2pAsm.Asm.Quic.Recovery
