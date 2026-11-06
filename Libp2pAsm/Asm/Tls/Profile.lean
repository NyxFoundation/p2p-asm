import Libp2pAsm.Asm.Tls.Messages

namespace Libp2pAsm.Asm.Tls.Profile
open Rv64 Crypto.Util Crypto.Link Cursor

def equal (slot n : Nat) : SAsm.Stmt := sequence [get slot .x11,
  block (load .x7 n), guard (.ne .x11 .x7) 7]
def present (slot : Nat) : SAsm.Stmt := sequence [get slot .x11, guard (.eq .x11 .x0) 7]
def nonzeroMask (slot mask : Nat) : SAsm.Stmt := sequence [get slot .x11,
  block [.ANDI .x11 .x11 (imm mask)], guard (.eq .x11 .x0) 7]

def group : Part := .seq [.asm (get 54 .x14), .asm (block [.ADDI .x15 .x0 0]),
  .seq ([23,29].map fun n => eqConst .x14 n (.asm (block [.ADDI .x15 .x0 1]))),
  .asm (guard (.eq .x15 .x0) 7)]

def client : Part := .seq [
  .asm (equal 5 0x1301), .asm (equal 62 1), .asm (present 61),
  .asm (nonzeroMask 60 11), .asm (present 63), .asm (present 34), .asm (present 26),
  .asm (get 57 .x12), when (.ne .x12 .x0) (.asm (nonzeroMask 61 1)),
  .asm (get 59 .x12), when (.ne .x12 .x0) (.asm (nonzeroMask 61 2))]

def server : Part := .seq [.asm (equal 62 1),
  slotEq 2 0 (.seq [.asm (equal 11 1), group]),
  slotEq 2 1 (.seq [
    .asm (sequence [get 26 .x11, get 36 .x12, block [.OR .x11 .x11 .x12], guard (.eq .x11 .x0) 7]),
    .asm (get 26 .x12), when (.ne .x12 .x0) group])]

def validate : Part := .seq [
  slotEq 0 1 client, slotEq 0 2 server,
  slotEq 0 8 (.asm (sequence [equal 63 1, present 34])),
  slotEq 0 13 (.asm (sequence [equal 39 0, nonzeroMask 60 11])),
  slotEq 0 11 (.asm (sequence [equal 39 0, equal 10 1])), .asm .ret]

end Libp2pAsm.Asm.Tls.Profile
