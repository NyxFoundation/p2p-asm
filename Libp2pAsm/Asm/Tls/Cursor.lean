import Libp2pAsm.Asm.Tls.Common

namespace Libp2pAsm.Asm.Tls.Cursor
open Rv64 Crypto.Util Crypto.Link

def outputBytes : Nat := 512
/-- 512-byte view, plus two complete uint16-ID bitmaps. No small vector cap. -/
def workspaceBytes : Nat := 16896
def stackBytes : Nat := 240

/-- x27 is the post-enter stack pointer, invariant across all parser routines.
Clear the complete owned call area even when failing several calls deep. -/
def cleanup : SAsm.Stmt := sequence [
  block (load .x11 workspaceBytes), wipe .x19 .x11,
  block [.ADDI .x12 .x27 (-128), .ADDI .x11 .x0 128], wipe .x12 .x11,
  block [.ADDI .x2 .x27 0], leave]

def fail (status : Nat) : SAsm.Stmt := sequence [block [.ADDI .x10 .x0 (imm status)], cleanup]
def guard (bad : SAsm.Cond) (status : Nat := 2) : SAsm.Stmt := .ite bad (fail status) empty

def need (count : Reg) : SAsm.Stmt := sequence [
  block [.SUB .x5 .x18 .x9], guard (.ltu .x5 count)]

/-- Source offsets, not wrapping end pointers: x8=base, x9=pos, x18=stop.
Each caller establishes 0 <= pos <= stop <= uint24+4, and a nonwrapping base.
Only t0/t1/t2 are scratch; result must be another register. -/
def read (width : Nat) (dst : Reg) : SAsm.Stmt := sequence [
  block [.ADDI .x7 .x0 (imm width)], need .x7,
  block ([.ADD .x5 .x8 .x9, .ADDI dst .x0 0] ++
    (List.range width).flatMap (fun i => [.LBU .x6 .x5 (imm i), .SLLI dst dst 8, .OR dst dst .x6]) ++
    [.ADDI .x9 .x9 (imm width)])]

def put (slot : Nat) (src : Reg) : SAsm.Stmt := block [.SD .x19 src (imm (slot*8))]
def get (slot : Nat) (dst : Reg) : SAsm.Stmt := block [.LD dst .x19 (imm (slot*8))]
def set (slot value : Nat) : SAsm.Stmt := sequence [block (load .x11 value), put slot .x11]

def span (slot : Nat) (count : Reg) : SAsm.Stmt := sequence [need count,
  block [.SD .x19 .x9 (imm (8*slot)), .SD .x19 count (imm (8*(slot+1))), .ADD .x9 .x9 count]]

def take (slot count : Nat) : SAsm.Stmt := sequence [block (load .x11 count), span slot .x11]

def vector (slot width minimum : Nat) : SAsm.Stmt := sequence [read width .x11,
  block (load .x7 minimum), guard (.ltu .x11 .x7), span slot .x11]

def done : SAsm.Stmt := guard (.ne .x9 .x18)

/-- Save the caller's actual return address, then use frozen PIC Link calls.
The parser has at most five nested calls (80 bytes), reserved area is 128. -/
def invoke (target : Nat) : Part := .seq [
  .asm (block [.ADDI .x2 .x2 (-16), .SD .x2 .x1 0, .SD .x2 .x0 8]), .call target,
  .asm (block [.LD .x1 .x2 0, .SD .x2 .x0 0, .SD .x2 .x0 8, .ADDI .x2 .x2 16])]

/-- Put the potentially large body on the JAL arm of the typed SAsm conditional. -/
def when (condition : SAsm.Cond) (body : Part) : Part := .ite condition.neg (.asm empty) body

def eqConst (r : Reg) (n : Nat) (body : Part) : Part := .seq [
  .asm (block (load .x7 n)), when (.eq r .x7) body]

def slotEq (slot n : Nat) (body : Part) : Part := .seq [.asm (get slot .x12), eqConst .x12 n body]

/-- Mark a uint16 ID in a complete 65536-bit bitmap. All address arithmetic is
within the checked workspace. Reject duplicates before setting the bit. -/
def mark (offset : Nat) (id : Reg) : SAsm.Stmt := sequence [
  block (load .x6 offset ++ [.ADD .x6 .x19 .x6, .SRLI .x5 id 3, .ADD .x5 .x5 .x6,
    .ANDI .x6 id 7, .ADDI .x7 .x0 1, .SLL .x6 .x7 .x6, .LBU .x7 .x5 0,
    .AND .x28 .x7 .x6]), guard (.ne .x28 .x0) 6,
  block [.OR .x7 .x7 .x6, .SB .x5 .x7 0]]

end Libp2pAsm.Asm.Tls.Cursor
