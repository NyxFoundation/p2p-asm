import Libp2pAsm.Asm.Quic.Wire.Common

namespace Libp2pAsm.Asm.Quic.Wire.Writer
open Rv64 Crypto.Util

/-- Entire declared workspace is owned and wiped, making the failure footprint
independent of which later source field fails. Capacity is charged to admission. -/
def enter (headerBytes : Nat) : P := seq [Wire.enter 0, .asm (wipe .x20 .x21),
  li .x7 headerBytes, reject (.ltu .x9 .x7) 1]

/-- Encoder input is a little-endian descriptor and relative byte views in one
mapped source span. Descriptor itself can be unaligned. x22 stays zero so encoding
errors report offset zero; individual field validity is independent of parse cursors. -/
def field (word : Nat) : P := seq [li .x7 (8*word+8), reject (.ltu .x9 .x7) 1,
  ins ([.ADDI .x10 .x0 0] ++ (List.range 8).flatMap (fun i =>
    [.LBU .x5 .x8 (imm (word*8+i)), .SLLI .x5 .x5 (BitVec.ofNat 6 (8*i)),
      .OR .x10 .x10 .x5]))]

def saveField (word slot : Nat) : P := seq [field word, ins [.SD .x2 .x10 (imm slot)]]

def fieldAt : P := seq [li .x7 8, reject (.ltu .x9 .x7) 1,
  ins [.ADDI .x7 .x9 (-8)], reject (.ltu .x7 .x10) 1,
  ins ([.ADD .x6 .x8 .x10, .ADDI .x10 .x0 0] ++ (List.range 8).flatMap (fun i =>
    [.LBU .x5 .x6 (imm i), .SLLI .x5 .x5 (BitVec.ofNat 6 (8*i)), .OR .x10 .x10 .x5]))]

/-- Reserve x10 bytes; capacity subtraction precedes all arithmetic/writes. -/
def reserve : P := seq [ins [.SUB .x5 .x19 .x23, .SUB .x6 .x21 .x23],
  reject (.ltu .x5 .x10) 5, reject (.ltu .x6 .x10) 5,
  ins [.ADDI .x11 .x23 0, .ADD .x23 .x23 .x10]]

def byte : P := seq [mov .x12 .x10, li .x10 1, reserve,
  ins [.ADD .x5 .x20 .x11, .SB .x5 .x12 0]]

def byteN (n : Nat) : P := seq [li .x10 n, byte]

def integer : P := seq [ins [.ADD .x11 .x20 .x23, .SUB .x12 .x19 .x23,
  .SUB .x5 .x21 .x23], .ite (.ltu .x5 .x12) (mov .x12 .x5) emptyP,
  .call 1, li .x7 2, reject (.eq .x10 .x7) 3, reject (.ne .x10 .x0) 5,
  ins [.ADD .x23 .x23 .x11]]

def integerField (word : Nat) : P := seq [field word,integer]

def be (n : Nat) : P := seq [mov .x12 .x10, li .x10 n, reserve,
  ins ([.ADD .x5 .x20 .x11] ++ storeBE .x5 .x12 0 n)]

/-- a0=offset,a1=length, both checked against the complete mapped source span. -/
def view : P := seq [reject (.ltu .x9 .x11) 1,
  ins [.SUB .x5 .x9 .x11], reject (.ltu .x5 .x10) 1,
  ins [.SD .x2 .x10 216, .SD .x2 .x11 224], mov .x10 .x11, reserve,
  ins [.ADD .x12 .x20 .x11, .LD .x13 .x2 216, .ADD .x13 .x8 .x13,
    .LD .x14 .x2 224], .asm (copy .x12 .x13 .x14)]

def viewField (word : Nat) : P := seq [saveField word 208, field (word+1),
  mov .x11 .x10, ins [.LD .x10 .x2 208], view]

/-- Validate a descriptor view even when its packet kind does not emit it. -/
def checkViewField (word : Nat) : P := seq [saveField word 208, field (word+1),
  reject (.ltu .x9 .x10) 1, ins [.SUB .x5 .x9 .x10, .LD .x6 .x2 208],
  reject (.ltu .x5 .x6) 1]

def finish : P := seq [.asm (copy .x18 .x20 .x23),
  .asm (wipe .x20 .x23), li .x10 0, li .x11 0, mov .x12 .x23, leave]

/-- Swap conditional arms to keep the conditional branch short; the JAL crosses
the long arm. Only existing typed RV64 branches and jumps are emitted. -/
def relax : P → P
  | .seq xs => .seq (xs.map relax)
  | .ite c a b =>
    let a := relax a
    let b := relax b
    if a.size+2 ≥ 1024 then .ite c.neg b a else .ite c a b
  | .loop c b => .loop c (relax b)
  | p => p

def link (root : P) (extra : List P := []) : Except String SAsm.Stmt :=
  Crypto.Link.program (relax root)
    ([.asm Codec.QuicVarint.decode,.asm Codec.QuicVarint.encode] ++ extra.map relax)

end Libp2pAsm.Asm.Quic.Wire.Writer
