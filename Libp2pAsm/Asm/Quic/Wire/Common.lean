import Libp2pAsm.Asm.Crypto.Link
import Libp2pAsm.Asm.Codec.QuicVarint

namespace Libp2pAsm.Asm.Quic.Wire
open Rv64 Crypto.Util Crypto.Link

abbrev P := Part
def ins (xs : List Instr) : P := .asm (.block xs)
def seq (xs : List P) : P := .seq xs
def li (r : Reg) (n : Nat) : P := ins (load r n)
def mov (dst src : Reg) : P := ins [.ADDI dst src 0]
def emptyP : P := ins []

/-- a0=status, a1=error offset (0 on success), a2=consumed/written (0 on error).
All other caller temporaries are zeroed. s0..s11, sp, ra, gp, tp are preserved. -/
def leave : P := seq [ins <|
  (saved.zipIdx.flatMap fun (r,i) => [.LD r .x2 (imm (i*8))]) ++
  ((List.range 32).map fun i => .SD .x2 .x0 (imm (i*8))) ++
  [.ADDI .x2 .x2 256] ++
  ((Crypto.Sha2.cleared.filter fun r => r != .x10 && r != .x11 && r != .x12).map
    fun r => .ADDI r .x0 0), .asm .ret]

def early (status : Nat) : P := seq [ins <|
  [.ADDI .x10 .x0 (imm status), .ADDI .x11 .x0 0, .ADDI .x12 .x0 0] ++
  ((Crypto.Sha2.cleared.filter (· != .x10)).map fun r => .ADDI r .x0 0), .asm .ret]

def fail (status : Nat) : P := seq [
  .asm (wipe .x20 .x23), li .x10 status, mov .x11 .x22, li .x12 0, leave]

def reject (c : SAsm.Cond) (status : Nat := 3) : P := .ite c (fail status) emptyP
def earlyReject (c : SAsm.Cond) (status : Nat) : P := .ite c (early status) emptyP

def checkRange (ptr len : Reg) : P := .ite (.ne len .x0) (seq [
  ins [.ADDI .x5 .x0 (-1), .SUB .x5 .x5 ptr, .ADDI .x6 len (-1)],
  earlyReject (.ltu .x5 .x6) 4]) emptyP

/-- Subtraction-based overlap check, valid even when a range ends at 2^64. -/
def disjoint (p n q m : Reg) : P := .ite (.ne n .x0) (.ite (.ne m .x0)
  (.ite (.ltu p q)
    (seq [ins [.SUB .x5 q p], earlyReject (.ltu .x5 n) 6])
    (seq [ins [.SUB .x5 p q], earlyReject (.ltu .x5 m) 6])) emptyP) emptyP

/-- Public ABI a0=input,a1=input length,a2=output,a3=output cap,a4=aligned work,
a5=work cap,a6=option,a7=iteration/range capacity. No memory access before preflight. -/
def enter (minimum : Nat) : P := seq [
  checkRange .x10 .x11, checkRange .x12 .x13, checkRange .x14 .x15,
  li .x7 minimum, earlyReject (.ltu .x13 .x7) 5, earlyReject (.ltu .x15 .x7) 5,
  ins [.ANDI .x5 .x14 7], earlyReject (.ne .x5 .x0) 6,
  ins [.ANDI .x5 .x2 15], earlyReject (.ne .x5 .x0) 6,
  li .x7 256, earlyReject (.ltu .x2 .x7) 4,
  ins [.ADDI .x28 .x2 (-256)],
  disjoint .x10 .x11 .x12 .x13, disjoint .x10 .x11 .x14 .x15,
  disjoint .x12 .x13 .x14 .x15,
  disjoint .x28 .x7 .x10 .x11, disjoint .x28 .x7 .x12 .x13,
  disjoint .x28 .x7 .x14 .x15,
  ins ([.ADDI .x2 .x2 (-256)] ++ saved.zipIdx.map (fun (r,i) => .SD .x2 r (imm (i*8)))),
  ins [.ADDI .x8 .x10 0, .ADDI .x9 .x11 0, .ADDI .x18 .x12 0,
    .ADDI .x19 .x13 0, .ADDI .x20 .x14 0, .ADDI .x21 .x15 0,
    .ADDI .x26 .x16 0, .ADDI .x27 .x17 0, .ADDI .x22 .x0 0],
  li .x23 minimum, .asm (wipe .x20 .x23)]

def put (word : Nat) (r : Reg) : P := ins [.SD .x20 r (imm (word*8))]
def getWord (r : Reg) (word : Nat) : P := ins [.LD r .x20 (imm (word*8))]
def putN (word n : Nat) : P := seq [li .x7 n, put word .x7]

/-- x10=count, x22=cursor. Takes checked source span, returns x11=start.
All source accesses follow this subtraction-based check. -/
def take : P := seq [ins [.SUB .x5 .x9 .x22], reject (.ltu .x5 .x10) 1,
  ins [.ADDI .x11 .x22 0, .ADD .x22 .x22 .x10]]

def takeN (n : Nat) : P := seq [li .x10 n, take]
def readByte : P := seq [takeN 1, ins [.ADD .x5 .x8 .x11, .LBU .x10 .x5 0]]

/-- Calls the frozen QUIC varint leaf after range/remaining validation. -/
def readInt : P := seq [ins [.ADD .x10 .x8 .x22, .SUB .x11 .x9 .x22],
  .call 0, reject (.ne .x10 .x0) 1,
  ins [.ADD .x22 .x22 .x12, .ADDI .x10 .x11 0]]

def readBE (n : Nat) : P := seq [takeN n,
  ins ([.ADD .x5 .x8 .x11, .ADDI .x10 .x0 0] ++
    (List.range n).flatMap (fun i => [.SLLI .x10 .x10 8,
      .LBU .x6 .x5 (imm i), .OR .x10 .x10 .x6]))]

def storeView (word : Nat) : P := seq [take, put word .x11, put (word+1) .x10]
def rest : P := ins [.SUB .x10 .x9 .x22]
def readStore (word : Nat) : P := seq [readInt, put word .x10]

def publish : P := seq [put 0 .x22, .asm (copy .x18 .x20 .x23),
  .asm (wipe .x20 .x23), li .x10 0, li .x11 0, mov .x12 .x22, leave]

def link (root : P) (extras : List P := []) : Except String SAsm.Stmt :=
  Crypto.Link.program root (.asm Codec.QuicVarint.decode :: extras)

end Libp2pAsm.Asm.Quic.Wire
