import Libp2pAsm.Asm.Kernel.Generation
import Libp2pAsm.Asm.Buffer

namespace Libp2pAsm.Asm.Kernel
open Rv64

/-- Header 128 bytes, then unchanged resolver descriptors, then 32-byte borrow records. -/
def registrySlot : SAsm.Stmt := seq [input .x24 0,get .x25 0,reject (.geu .x24 .x25) 13,
  ins [.SLLI .x26 .x24 5,.ADD .x26 .x8 .x26,.ADDI .x26 .x26 128,
    .SLLI .x27 .x25 5,.ADD .x27 .x26 .x27],
  input .x24 1,ins [.LD .x25 .x26 0],reject (.ne .x24 .x25) 14]

def noBorrow : SAsm.Stmt := seq [ins [.LD .x5 .x27 0,.LD .x6 .x27 8,.LD .x7 .x27 16,
  .OR .x5 .x5 .x6,.OR .x5 .x5 .x7],reject (.ne .x5 .x0) 15]

def noPending : SAsm.Stmt := seq [get .x5 8,reject (.ne .x5 .x0) 15,get .x5 15,reject (.ne .x5 .x0) 15]

def checkDisjoint (a n b m : Reg) : SAsm.Stmt := .ite (.ltu a b)
  (seq [ins [.SUB .x5 b a],reject (.ltu .x5 n) 18])
  (seq [ins [.SUB .x5 a b],reject (.ltu .x5 m) 18])

def registryBegin : SAsm.Stmt := seq [enter 128 40 0,noPending,registrySlot,
  ins [.LD .x5 .x26 24],reject (.ne .x5 .x0) 15,noBorrow,
  ins [.LD .x5 .x27 24],reject (.ne .x5 .x0) 16,
  input .x24 2,input .x25 3,input .x28 4,li .x7 1,reject (.ltu .x7 .x28) 9,
  reject (.eq .x25 .x0) 9,ins [.ADD .x29 .x24 .x25],reject (.ltu .x29 .x24) 9,
  get .x28 4,get .x29 5,checkDisjoint .x24 .x25 .x28 .x29,
  get .x28 6,get .x29 7,checkDisjoint .x24 .x25 .x28 .x29,
  putN 8 1,input .x24 0,put 9 .x24,input .x24 2,put 10 .x24,
  input .x24 3,put 11 .x24,input .x24 4,put 12 .x24,putN 13 0,input .x24 1,put 14 .x24,
  li .x24 1,success .x24 .x0]

def clearPending : SAsm.Stmt := ins ((List.range 7).map fun i => .SD .x8 .x0 (imm (64+i*8)))

def scanAbort : SAsm.Stmt := seq [clearPending,li .x24 2,li .x25 18,success .x24 .x25]

def scanOverlap : SAsm.Stmt := seq [
  get .x24 10,get .x25 11,ins [.LD .x28 .x26 8,.LD .x29 .x26 16],
  .ite (.ltu .x24 .x28)
    (seq [ins [.SUB .x5 .x28 .x24],.ite (.ltu .x5 .x25) scanAbort empty])
    (seq [ins [.SUB .x5 .x24 .x28],.ite (.ltu .x5 .x29) scanAbort empty])]

def registryResume : SAsm.Stmt := seq [enter 128 0 0,get .x5 8,li .x6 1,reject (.ne .x5 .x6) 14,
  get .x22 13,get .x23 0,li .x27 32,
  .loop (.ltu .x22 .x23) (seq [
    .ite (.eq .x27 .x0) (seq [put 13 .x22,li .x24 1,success .x24 .x22]) empty,
    ins [.SLLI .x26 .x22 5,.ADD .x26 .x8 .x26,.ADDI .x26 .x26 128,.LD .x5 .x26 24],
    .ite (.ne .x5 .x0) (seq [get .x6 12,ins [.SRLI .x5 .x5 1,.OR .x5 .x5 .x6],
      .ite (.ne .x5 .x0) scanOverlap empty]) empty,
    ins [.ADDI .x22 .x22 1,.ADDI .x27 .x27 (-1)]]),
  get .x24 9,ins [.SLLI .x26 .x24 5,.ADD .x26 .x8 .x26,.ADDI .x26 .x26 128],
  get .x24 14,get .x25 10,get .x28 11,get .x29 12,
  ins [.SLLI .x29 .x29 1,.ADDI .x29 .x29 1,.SD .x26 .x24 0,.SD .x26 .x25 8,
    .SD .x26 .x28 16,.SD .x26 .x29 24],
  get .x24 1,ins [.ADDI .x24 .x24 1],put 1 .x24,clearPending,success .x0 .x0]

def registryUnregister : SAsm.Stmt := seq [noBorrow,
  ins [.LD .x10 .x26 0],ins generationCode,
  ins [.SD .x26 .x10 0,.SD .x27 .x11 24],
  ins [.SD .x26 .x0 8,.SD .x26 .x0 16,.SD .x26 .x0 24],
  get .x24 1,ins [.ADDI .x24 .x24 (-1)],put 1 .x24,success .x0 .x0]

def borrow (kind : Nat) (acquire : Bool) : SAsm.Stmt := seq [
  ins [.LD .x24 .x27 (imm (kind*8))],
  if acquire then seq [reject (.ne .x24 .x0) 15,
    if kind == 2 then seq [ins [.LD .x5 .x26 24],li .x6 3,
      reject (.ne .x5 .x6) 21,noBorrow]
    else seq [ins [.LD .x5 .x27 16],reject (.ne .x5 .x0) 15]]
  else seq [li .x5 1,reject (.ne .x24 .x5) 14],
  li .x24 (if acquire then 1 else 0),ins [.SD .x27 .x24 (imm (kind*8))],
  if kind < 2 then seq [get .x24 (2+kind),ins [.ADDI .x24 .x24 (if acquire then 1 else -1)],put (2+kind) .x24] else empty,
  success .x0 .x0]

def registryMutation (op : Nat) : SAsm.Stmt := seq [enter 128 16 0,(if op == 4 || op == 6 || op == 8 then empty else noPending),registrySlot,
  ins [.LD .x5 .x26 24],reject (.eq .x5 .x0) 14,
  if op == 2 then registryUnregister else borrow ((op-3)/2) (op%2 == 1)]

/-- End-of-step input borrows expire in bounded batches. Slot 15 owns the drain
cursor (index+1); callers must finish this drain before returning host buffers. -/
def registryEndStep : SAsm.Stmt := seq [enter 128 0 0,get .x22 15,
  .ite (.eq .x22 .x0) (li .x22 1) empty,ins [.ADDI .x22 .x22 (-1)],
  get .x23 0,li .x27 32,
  .loop (.ltu .x22 .x23) (seq [
    .ite (.eq .x27 .x0) (seq [ins [.ADDI .x24 .x22 1],put 15 .x24,li .x24 1,success .x24 .x22]) empty,
    ins [.ADD .x25 .x22 .x23,.SLLI .x25 .x25 5,.ADD .x26 .x8 .x25,.ADDI .x26 .x26 128,
      .LD .x5 .x26 0],
    .ite (.ne .x5 .x0) (seq [ins [.SD .x26 .x0 0],get .x24 2,
      ins [.ADDI .x24 .x24 (-1)],put 2 .x24]) empty,
    ins [.ADDI .x22 .x22 1,.ADDI .x27 .x27 (-1)]]),putN 15 0,success .x0 .x22]

end Libp2pAsm.Asm.Kernel
