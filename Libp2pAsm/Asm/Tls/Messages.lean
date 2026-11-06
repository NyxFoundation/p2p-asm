import Libp2pAsm.Asm.Tls.Extensions

namespace Libp2pAsm.Asm.Tls.Messages
open Rv64 Crypto.Util Crypto.Link Cursor

/-- Last uint16 extension vector; no trailing bytes permitted. -/
def extensionTail (typed : Bool) : Part := .seq [
  .asm (vector 20 2 0), .asm done,
  .asm (sequence [get 20 .x9, block [.ADDI .x25 .x0 (if typed then 1 else 0)]]), invoke 7]

def clientFields : Part := .seq [
  .asm (vector 16 2 2), .asm (get 17 .x11),
  .asm (block [.ANDI .x5 .x11 1]), .asm (guard (.ne .x5 .x0)),
  .asm (get 16 .x14), .asm (block [.ADD .x14 .x8 .x14, .ADD .x15 .x14 .x11]),
  .loop (.ltu .x14 .x15) (.seq [
    .asm (block [.LBU .x11 .x14 0, .SLLI .x11 .x11 8, .LBU .x6 .x14 1,
      .OR .x11 .x11 .x6, .ADDI .x14 .x14 2]),
    eqConst .x11 0x1301 (.asm (put 5 .x11))]),
  .asm (vector 18 1 1), .asm (get 19 .x11),
  .asm (block [.ADDI .x7 .x0 1]), .asm (guard (.ne .x11 .x7) 7),
  .asm (get 18 .x11), .asm (block [.ADD .x5 .x8 .x11, .LBU .x6 .x5 0]),
  .asm (guard (.ne .x6 .x0) 7)]

def serverFields : Part := .seq [
  .asm (read 2 .x11), .asm (put 5 .x11),
  .asm (block (load .x7 0x1301)), .asm (guard (.ne .x11 .x7) 7),
  .asm (read 1 .x11), .asm (put 6 .x11), .asm (guard (.ne .x11 .x0) 7)]

def retryRandom : SAsm.Stmt := sequence [
  block ([.ADDI .x14 .x0 0] ++
    ([0xcf,0x21,0xad,0x74,0xe5,0x9a,0x61,0x11,0xbe,0x1d,0x8c,0x02,0x1e,0x65,0xb8,0x91,
      0xc2,0xa2,0x11,0x16,0x7a,0xbb,0x8c,0x5e,0x07,0x9e,0x09,0xe2,0xc8,0xa8,0x33,0x9c].zipIdx.flatMap
      fun (b,i) => [.LBU .x6 .x8 (imm (6+i)), .XORI .x6 .x6 (imm b), .OR .x14 .x14 .x6])),
  .ite (.eq .x14 .x0) (set 2 1) empty]

def hello : Part := .seq [
  .asm (read 2 .x11), .asm (put 4 .x11),
  .asm (block (load .x7 0x0303)), .asm (guard (.ne .x11 .x7) 7),
  .asm (take 12 32), slotEq 0 2 (.asm retryRandom),
  .asm (vector 14 1 0), .asm (get 15 .x11),
  .asm (block [.ADDI .x7 .x0 32]), .asm (guard (.ltu .x7 .x11) 7),
  slotEq 0 1 clientFields, slotEq 0 2 serverFields,
  extensionTail true, .asm .ret]

def encryptedExtensions : Part := .seq [extensionTail true, .asm .ret]
def certificateRequest : Part := .seq [.asm (vector 38 1 0), extensionTail true, .asm .ret]

def certificateEntry : Part := .seq [
  .asm (read 3 .x11), .asm (guard (.eq .x11 .x0)), .asm (need .x11),
  slotEq 10 0 (.asm (Extensions.capture 42 .x11)),
  .asm (block [.ADD .x9 .x9 .x11]), .asm (read 2 .x11), .asm (need .x11),
  slotEq 10 0 (.asm (Extensions.capture 44 .x11)),
  .asm (block [.ADD .x18 .x9 .x11, .ADDI .x25 .x0 0]), invoke 7,
  .asm (sequence [get 10 .x11, block [.ADDI .x11 .x11 1], put 10 .x11,
    block [.ADDI .x18 .x21 0]]), .asm .ret]

def certificate : Part := .seq [
  .asm (vector 38 1 0), .asm (vector 40 3 0), .asm done, .asm (get 40 .x9),
  .loop (.ltu .x9 .x18) (invoke 14), .asm done, .asm .ret]

def certificateVerify : Part := .seq [
  .asm (read 2 .x14), .asm (put 7 .x14), .asm (vector 46 2 1), .asm done,
  .asm (block [.ADDI .x15 .x0 0]),
  .seq ([0x0403,0x0804,0x0807].map fun n => eqConst .x14 n (.asm (block [.ADDI .x15 .x0 1]))),
  .asm (guard (.eq .x15 .x0) 7), .asm .ret]

def finished : Part := .seq [.asm (take 48 32), .asm done, .asm .ret]

def ticket : Part := .seq [
  .asm (read 4 .x11), .asm (put 8 .x11),
  .asm (block (load .x7 604800)), .asm (guard (.ltu .x7 .x11) 7),
  .asm (read 4 .x11), .asm (put 9 .x11), .asm (vector 50 1 0),
  .asm (vector 52 2 1), extensionTail false, .asm .ret]

end Libp2pAsm.Asm.Tls.Messages
