import Libp2pAsm.Asm.Kernel.Common

namespace Libp2pAsm.Asm.Kernel
open Rv64

/-- x27 points to a window, x22=validated monotonic time, x28=window width. -/
def rotateWindow : SAsm.Stmt := seq [ins [.LD .x5 .x27 0,.SUB .x6 .x22 .x5],
  .ite (.geu .x6 .x28) (seq [ins [.DIVU .x6 .x6 .x28],li .x7 1,
    .ite (.eq .x6 .x7)
      (ins [.LD .x5 .x27 8,.LD .x6 .x27 16,.SD .x27 .x5 24,.SD .x27 .x6 32])
      (ins [.SD .x27 .x0 24,.SD .x27 .x0 32]),
    ins [.REMU .x5 .x22 .x28,.SUB .x5 .x22 .x5,.SD .x27 .x5 0,
      .SD .x27 .x0 8,.SD .x27 .x0 16]]) empty]

/-- x24/x25 limits, x23=datagram length. Count every datagram, saturating aggregates. -/
def countWindow : SAsm.Stmt := seq [ins [.LD .x5 .x27 8,.LD .x6 .x27 24,.ADD .x7 .x5 .x6],
  .ite (.ltu .x7 .x5) (li .x29 1) empty,
  .ite (.geu .x7 .x24) (li .x29 1) empty,
  ins [.LD .x5 .x27 16,.LD .x6 .x27 32,.ADD .x7 .x5 .x6],
  .ite (.ltu .x7 .x5) (li .x29 1) empty,
  .ite (.ltu .x25 .x7) (li .x29 1)
    (seq [ins [.SUB .x6 .x25 .x7],.ite (.ltu .x6 .x23) (li .x29 1) empty]),
  ins [.LD .x5 .x27 8,.ADDI .x6 .x0 (-1)],
  .ite (.ne .x5 .x6) (ins [.ADDI .x5 .x5 1]) empty,ins [.SD .x27 .x5 8],
  ins [.LD .x5 .x27 16,.ADD .x6 .x5 .x23],
  .ite (.ltu .x6 .x5) (ins [.ADDI .x6 .x0 (-1)]) empty,ins [.SD .x27 .x6 16]]

def saturateAt (p : Reg) (off : Nat) : SAsm.Stmt := seq [ins [.LD .x5 p (imm off),.ADDI .x6 .x0 (-1)],
  .ite (.ne .x5 .x6) (ins [.ADDI .x5 .x5 1]) empty,ins [.SD p .x5 (imm off)]]

def admitDatagram : SAsm.Stmt := seq [enter 256 32 0,input .x24 0,get .x25 0,
  reject (.geu .x24 .x25) 13,ins [.SLLI .x26 .x24 7,.ADD .x26 .x8 .x26,.ADDI .x26 .x26 256],
  input .x22 1,input .x23 2,get .x24 6,reject (.ltu .x22 .x24) 24,
  ins [.LD .x24 .x26 40],reject (.ltu .x22 .x24) 24,
  get .x28 10,ins [.ADDI .x27 .x8 8],rotateWindow,mov .x27 .x26,rotateWindow,
  li .x29 0,get .x24 8,get .x25 9,ins [.ADDI .x27 .x8 8],countWindow,
  get .x24 25,get .x25 26,mov .x27 .x26,countWindow,
  get .x24 7,get .x25 11,.ite (.geu .x24 .x25) (li .x29 2) empty,
  get .x24 28,.ite (.ltu .x24 .x23) (li .x29 3) empty,
  input .x24 3,.ite (.ne .x24 .x0) (li .x29 4) empty,
  put 6 .x22,ins [.SD .x26 .x22 40],saturateAt .x8 56,
  .ite (.ne .x29 .x0) (seq [saturateAt .x8 96,saturateAt .x26 88,li .x24 1,success .x24 .x29])
    (success .x0 .x0)]

/-- Caller-supplied cost is a certified or conservative estimated charge. This leaf
checks arithmetic/admission; it does not turn timings or an integer into a proof.
Header 128; connection slots64=(generation,phase,source,epoch,used,0,0,0). -/
def charge : SAsm.Stmt := seq [enter 128 40 0,input .x24 0,get .x25 0,reject (.geu .x24 .x25) 13,
  ins [.SLLI .x26 .x24 6,.ADD .x26 .x8 .x26,.ADDI .x26 .x26 128],
  input .x24 1,ins [.LD .x25 .x26 0],reject (.ne .x24 .x25) 14,
  ins [.LD .x25 .x26 8],reject (.eq .x25 .x0) 14,li .x5 3,reject (.geu .x25 .x5) 14,
  input .x22 2,get .x24 1,reject (.ltu .x22 .x24) 24,
  ins [.LD .x25 .x26 24],reject (.ltu .x22 .x25) 24,
  get .x28 4,get .x24 2,ins [.LD .x25 .x26 32],
  get .x5 1,ins [.SUB .x5 .x22 .x5],.ite (.geu .x5 .x28) (li .x24 0) empty,
  ins [.LD .x5 .x26 24,.SUB .x5 .x22 .x5],.ite (.geu .x5 .x28) (li .x25 0) empty,
  input .x23 3,reject (.eq .x23 .x0) 19,
  get .x5 7,ins [.SUB .x5 .x5 .x24],reject (.ltu .x5 .x23) 19,
  get .x5 6,ins [.SUB .x5 .x5 .x25],reject (.ltu .x5 .x23) 19,
  get .x5 5,get .x6 3,ins [.SUB .x5 .x5 .x6],reject (.ltu .x5 .x23) 19,
  input .x27 4,get .x5 8,get .x6 9,ins [.SUB .x5 .x5 .x6],reject (.ltu .x5 .x27) 19,
  ins [.ADD .x24 .x24 .x23,.ADD .x25 .x25 .x23],put 2 .x24,ins [.SD .x26 .x25 32],
  get .x5 3,ins [.ADD .x5 .x5 .x23],put 3 .x5,
  get .x5 9,ins [.ADD .x5 .x5 .x27],put 9 .x5,
  get .x5 1,ins [.SUB .x6 .x22 .x5],.ite (.geu .x6 .x28) (put 1 .x22) empty,
  ins [.LD .x5 .x26 24,.SUB .x6 .x22 .x5],
  .ite (.geu .x6 .x28) (ins [.SD .x26 .x22 24]) empty,success .x23 .x27]

/-- Start a new quantum and visit exactly one connection in round-robin order.
Inactive connections produce an explicit skip; no scan or busy loop is hidden. -/
def nextQuantum : SAsm.Stmt := seq [enter 128 0 0,get .x24 10,get .x25 0,
  ins [.ADDI .x26 .x24 1,.REMU .x26 .x26 .x25],put 10 .x26,putN 3 0,putN 9 0,
  ins [.SLLI .x26 .x24 6,.ADD .x26 .x8 .x26,.ADDI .x26 .x26 128,
    .LD .x25 .x26 8],success .x24 .x25]

end Libp2pAsm.Asm.Kernel
