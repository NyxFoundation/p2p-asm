import Libp2pAsm.Asm.Tls.Cursor

namespace Libp2pAsm.Asm.Tls.Extensions
open Rv64 Crypto.Util Crypto.Link Cursor

/-- Callee IDs 7=scan,8=entry,9=versions,10=uint16Offers,11=shares,
12=ALPN,13=cookie,14=certificateEntry,15=shareEntry,16=nameEntry,17=profile. -/
def capture (slot : Nat) (length : Reg) : SAsm.Stmt := block [
  .SD .x19 .x9 (imm (slot*8)), .SD .x19 length (imm ((slot+1)*8))]

def exactVector (slot width minimum : Nat) : SAsm.Stmt := sequence [
  read width .x11, block (load .x7 minimum), guard (.ltu .x11 .x7),
  need .x11, capture slot .x11,
  block [.SUB .x5 .x18 .x9], guard (.ne .x11 .x5)]

def maskValue (slot value bit : Nat) : Part := eqConst .x14 value (.asm (sequence [
  get slot .x15, block [.ORI .x15 .x15 (imm bit)], put slot .x15]))

def versions : Part := .seq [
  .asm (get 0 .x12), eqConst .x12 1 (.asm (exactVector 22 1 2)),
  eqConst .x12 2 (.asm (sequence [block [.ADDI .x11 .x0 2], need .x11, capture 22 .x11,
    block [.SUB .x5 .x18 .x9], guard (.ne .x11 .x5)])),
  .asm (get 23 .x11), .asm (block [.ANDI .x5 .x11 1]), .asm (guard (.ne .x5 .x0)),
  .loop (.ltu .x9 .x18) (.seq [.asm (read 2 .x14), maskValue 62 0x0304 1]),
  slotEq 0 2 (.asm (sequence [get 62 .x11, block [.ADDI .x7 .x0 1], guard (.ne .x11 .x7) 7])),
  .asm done, .asm .ret]

def offerWords : Part := .seq [
  eqConst .x22 10 (.asm (exactVector 24 2 2)),
  eqConst .x22 13 (.asm (exactVector 28 2 2)),
  eqConst .x22 50 (.asm (exactVector 30 2 2)),
  .asm (block [.SUB .x5 .x18 .x9, .ANDI .x5 .x5 1]), .asm (guard (.ne .x5 .x0)),
  .loop (.ltu .x9 .x18) (.seq [.asm (read 2 .x14),
    eqConst .x22 10 (.seq [maskValue 61 29 1, maskValue 61 23 2]),
    eqConst .x22 13 (.seq [maskValue 60 0x0403 1, maskValue 60 0x0804 2,
      maskValue 60 0x0401 4, maskValue 60 0x0807 8])]), .asm .ret]

def shareEntry : Part := .seq [
  .asm (read 2 .x14), .asm (read 2 .x11), .asm (guard (.eq .x11 .x0)), .asm (need .x11),
  eqConst .x14 29 (.asm (sequence [block [.ADDI .x7 .x0 32],
    guard (.ne .x11 .x7), capture 56 .x11])),
  eqConst .x14 23 (.asm (sequence [block [.ADDI .x7 .x0 65], guard (.ne .x11 .x7),
    block [.ADD .x5 .x8 .x9, .LBU .x6 .x5 0, .ADDI .x7 .x0 4], guard (.ne .x6 .x7),
    capture 58 .x11])),
  .asm (mark 8704 .x14),
  slotEq 0 2 (.asm (put 54 .x14)),
  .asm (sequence [get 11 .x15, block [.ADDI .x15 .x15 1], put 11 .x15,
    block [.ADD .x9 .x9 .x11]]), .asm .ret]

def shares : Part := .seq [
  .asm (block [.SUB .x11 .x18 .x9]), .asm (capture 26 .x11),
  slotEq 2 1 (.seq [.asm (read 2 .x14), .asm (put 54 .x14), .asm done, .asm .ret]),
  slotEq 0 1 (.asm (sequence [read 2 .x11, need .x11,
    block [.SUB .x5 .x18 .x9], guard (.ne .x11 .x5)])),
  slotEq 0 2 (invoke 15),
  slotEq 0 1 (.loop (.ltu .x9 .x18) (invoke 15)),
  .asm done, .asm .ret]

def nameEntry : Part := .seq [
  .asm (read 1 .x11), .asm (guard (.eq .x11 .x0)), .asm (need .x11),
  .asm (block [.ADDI .x7 .x0 6]),
  when (.eq .x11 .x7) (.seq [
    .asm (block ([.ADD .x5 .x8 .x9, .ADDI .x14 .x0 0] ++
      ([108,105,98,112,50,112].zipIdx.flatMap fun (b,i) =>
        [.LBU .x6 .x5 (imm i), .XORI .x6 .x6 (imm b), .OR .x14 .x14 .x6]))),
    when (.eq .x14 .x0) (.asm (sequence [get 63 .x14,
      block [.ADDI .x14 .x14 1], put 63 .x14]))]),
  .asm (block [.ADD .x9 .x9 .x11, .ADDI .x17 .x17 1]), .asm .ret]

def alpn : Part := .seq [
  .asm (block [.SUB .x11 .x18 .x9]), .asm (capture 32 .x11),
  .asm (read 2 .x11), .asm (block [.ADDI .x7 .x0 2]), .asm (guard (.ltu .x11 .x7)),
  .asm (need .x11), .asm (block [.SUB .x5 .x18 .x9]), .asm (guard (.ne .x11 .x5)),
  .asm (block [.ADDI .x17 .x0 0]),
  .loop (.ltu .x9 .x18) (invoke 16),
  slotEq 0 8 (.asm (sequence [block [.ADDI .x7 .x0 1], guard (.ne .x17 .x7)])),
  .asm .ret]

def cookie : Part := .seq [.asm (vector 36 2 1), .asm done, .asm .ret]

/-- Keep context validation separate from field grammar. Unknown ClientHello
extensions are skipped; unknown server extensions retain obligation bit 0. -/
def contexts : Part := .seq [
  slotEq 0 2 (.seq [
    .asm (block [.ADDI .x14 .x0 0]),
    eqConst .x22 43 (.asm (block [.ADDI .x14 .x0 1])),
    eqConst .x22 51 (.asm (block [.ADDI .x14 .x0 1])),
    slotEq 2 1 (eqConst .x22 44 (.asm (block [.ADDI .x14 .x0 1]))),
    .asm (guard (.eq .x14 .x0) 3)]),
  .asm (get 0 .x13),
  .seq ([43,51].map fun n => eqConst .x22 n (.seq [
    .asm (block [.ADDI .x7 .x0 1]), when (.ne .x13 .x7) (.asm (sequence [
      block [.ADDI .x7 .x0 2], guard (.ne .x13 .x7)]))])),
  eqConst .x22 44 (.seq [.asm (block [.ADDI .x7 .x0 1]), when (.ne .x13 .x7)
    (.asm (sequence [get 2 .x14, guard (.eq .x14 .x0)]))]),
  .seq ([13,50].map fun n => eqConst .x22 n (.seq [
    .asm (block [.ADDI .x7 .x0 1]), when (.ne .x13 .x7) (.asm (sequence [
      block [.ADDI .x7 .x0 13], guard (.ne .x13 .x7)]))])),
  .seq ([16,57,10].map fun n => eqConst .x22 n (.seq [
    .asm (block [.ADDI .x7 .x0 1]), when (.ne .x13 .x7) (.asm (sequence [
      block [.ADDI .x7 .x0 8], guard (.ne .x13 .x7)]))])),
  eqConst .x22 42 (.seq [.asm (block [.ADDI .x7 .x0 1]),
    when (.ne .x13 .x7) (.asm (sequence [block [.ADDI .x7 .x0 4], guard (.ne .x13 .x7)]))])]

def entry : Part := .seq [
  .asm (read 2 .x22), .asm (read 2 .x11), .asm (need .x11), .asm (mark 512 .x22),
  .asm (block [.ADD .x23 .x9 .x11, .ADDI .x18 .x23 0]),
  contexts,
  when (.ne .x25 .x0) (.seq [
    slotEq 0 1 (eqConst .x22 0 (.asm (set 55 1))),
    eqConst .x22 43 (invoke 9),
    .seq ([10,13,50].map fun n => eqConst .x22 n (invoke 10)),
    eqConst .x22 51 (invoke 11), eqConst .x22 16 (invoke 12),
    eqConst .x22 44 (invoke 13),
    eqConst .x22 57 (.asm (sequence [block [.SUB .x11 .x18 .x9], capture 34 .x11]))]),
  slotEq 0 4 (eqConst .x22 42 (.asm (sequence [
    block [.SUB .x11 .x23 .x9, .ADDI .x7 .x0 4], guard (.ne .x11 .x7)]))),
  .asm (block [.ADDI .x9 .x23 0, .ADDI .x18 .x24 0]), .asm .ret]

def scan : Part := .seq [
  .asm (block (load .x11 8192 ++ [.ADDI .x12 .x19 512])), .asm (wipe .x12 .x11),
  .asm (block [.ADDI .x24 .x18 0]),
  .loop (.ltu .x9 .x18) (invoke 8), .asm done, .asm .ret]

end Libp2pAsm.Asm.Tls.Extensions
