import Libp2pAsm.Asm.Kernel.Common

namespace Libp2pAsm.Asm.Kernel
open Rv64

/-- Quota leases only. A transition here neither authenticates a peer nor advances TLS. -/
def connectionSlot : SAsm.Stmt := seq [get .x5 0,li .x6 2,reject (.ne .x5 .x6) 14,
  get .x24 10,get .x25 11,ins [.ADD .x24 .x8 .x24,.ADD .x25 .x8 .x25],
  input .x5 0,ins [.LD .x6 .x25 0],reject (.geu .x5 .x6) 13,
  ins [.SLLI .x26 .x5 6,.ADD .x26 .x25 .x26,.ADDI .x26 .x26 128],
  input .x5 1,ins [.LD .x6 .x26 0],reject (.ne .x5 .x6) 14]

def sourceSlot (fromInput : Bool) : SAsm.Stmt := seq [
  if fromInput then input .x5 2 else ins [.LD .x5 .x26 16],
  ins [.LD .x6 .x24 0],reject (.geu .x5 .x6) 13,
  ins [.SLLI .x27 .x5 7,.ADD .x27 .x24 .x27,.ADDI .x27 .x27 256]]

def quota (usedPtr : Reg) (usedOff : Nat) (capPtr : Reg) (capOff : Nat) : SAsm.Stmt := seq [
  ins [.LD .x5 usedPtr (imm usedOff),.LD .x6 capPtr (imm capOff)],reject (.geu .x5 .x6) 19]

/-- Preview an epoch/current/previous triple in registers, never changing persistent
state on a refused handshake. x28=triple; x23=now; x22=window. -/
def previewStarts (stackOff : Nat) : SAsm.Stmt := seq [
  ins [.LD .x5 .x28 0,.LD .x6 .x28 8,.LD .x7 .x28 16],reject (.ltu .x23 .x5) 24,
  ins [.SUB .x29 .x23 .x5],
  .ite (.geu .x29 .x22) (seq [ins [.DIVU .x29 .x29 .x22],li .x30 1,
    .ite (.eq .x29 .x30) (mov .x7 .x6) (li .x7 0),li .x6 0,
    ins [.REMU .x5 .x23 .x22,.SUB .x5 .x23 .x5]]) empty,
  ins [.SD .x2 .x5 (imm stackOff),.SD .x2 .x6 (imm (stackOff+8)),.SD .x2 .x7 (imm (stackOff+16))]]

def startQuota (stackOff capOff : Nat) : SAsm.Stmt := seq [
  ins [.LD .x5 .x2 (imm (stackOff+8)),.LD .x6 .x2 (imm (stackOff+16)),.ADD .x7 .x5 .x6],
  reject (.ltu .x7 .x5) 19,ins [.LD .x5 .x24 (imm capOff)],reject (.geu .x7 .x5) 19]

def commitStarts (stackOff : Nat) : SAsm.Stmt := ins [
  .LD .x5 .x2 (imm stackOff),.LD .x6 .x2 (imm (stackOff+8)),.LD .x7 .x2 (imm (stackOff+16)),
  .ADDI .x6 .x6 1,.SD .x28 .x5 0,.SD .x28 .x6 8,.SD .x28 .x7 16]

def adjust (p : Reg) (off : Nat) (increment : Bool) : SAsm.Stmt := ins [
  .LD .x5 p (imm off),.ADDI .x5 .x5 (if increment then 1 else -1),.SD p .x5 (imm off)]

def connectionAcquire : SAsm.Stmt := seq [enter 176 32 0,get .x5 20,reject (.ne .x5 .x0) 15,connectionSlot,
  ins [.LD .x5 .x26 8],li .x6 3,reject (.eq .x5 .x6) 16,reject (.ne .x5 .x0) 15,
  sourceSlot true,input .x23 3,ins [.LD .x22 .x24 160],
  ins [.LD .x5 .x24 48],reject (.ltu .x23 .x5) 24,
  quota .x24 176 .x24 184,quota .x27 80 .x24 192,
  quota .x24 168 .x24 128,quota .x27 72 .x24 136,
  ins [.ADDI .x28 .x24 104],previewStarts 128,startQuota 128 144,
  ins [.ADDI .x28 .x27 48],previewStarts 152,startQuota 152 152,
  ins [.ADDI .x28 .x24 104],commitStarts 128,
  ins [.ADDI .x28 .x27 48],commitStarts 152,
  adjust .x24 176 true,adjust .x27 80 true,adjust .x24 168 true,adjust .x27 72 true,
  li .x5 1,ins [.SD .x26 .x5 8],input .x5 2,
  ins [.SD .x26 .x5 16,.SD .x26 .x23 24,.SD .x26 .x0 32,.SD .x26 .x0 40,.SD .x26 .x0 48,.SD .x26 .x0 56],
  input .x24 0,input .x25 1,success .x24 .x25]

def releaseQuotaCore : SAsm.Stmt := seq [li .x5 1,.ite (.eq .x22 .x5) (seq [adjust .x24 168 false,adjust .x27 72 false]) empty,
    adjust .x24 176 false,adjust .x27 80 false,
    ins [.LD .x5 .x26 0,.ADDI .x6 .x0 (-1)],
    .ite (.eq .x5 .x6) (seq [li .x7 3,ins [.SD .x26 .x7 8]])
      (ins [.ADDI .x5 .x5 1,.SD .x26 .x5 0,.SD .x26 .x0 8]),
    ins ((List.range 6).map fun i => .SD .x26 .x0 (imm (16+i*8)))]

def connectionRelease (handshakeOnly : Bool) : SAsm.Stmt := seq [enter 160 16 0,connectionSlot,
  ins [.LD .x22 .x26 8],reject (.eq .x22 .x0) 14,li .x5 3,reject (.geu .x22 .x5) 14,
  sourceSlot false,
  if handshakeOnly then seq [li .x5 1,reject (.ne .x22 .x5) 14,
    adjust .x24 168 false,adjust .x27 72 false,li .x5 2,ins [.SD .x26 .x5 8],success .x0 .x0]
  else seq [releaseQuotaCore,success .x0 .x0]]

/-- One connection quota lease per call. Returned owner handles are obligations for
main's TLS/core cleanup; no TLS state is claimed to have been erased here. Allocation
is locked until the owned walk reaches the end. Output is mandatory, never queued. -/
def connectionCleanup : SAsm.Stmt := seq [enter 176 0 32,get .x5 0,li .x6 2,reject (.ne .x5 .x6) 14,
  get .x5 20,.ite (.eq .x5 .x0) (seq [li .x6 1,reject (.ltu .x22 .x6) 12,
    li .x6 2,reject (.ltu .x6 .x22) 12,put 20 .x22,putN 21 0]) empty,
  get .x24 10,get .x25 11,ins [.ADD .x24 .x8 .x24,.ADD .x25 .x8 .x25],
  get .x23 21,ins [.LD .x5 .x25 0],
  .ite (.geu .x23 .x5) (seq [putN 20 0,putN 21 0,success .x0 .x0]) empty,
  ins [.SLLI .x26 .x23 6,.ADD .x26 .x25 .x26,.ADDI .x26 .x26 128,
    .LD .x22 .x26 8,.ADDI .x5 .x23 1],put 21 .x5,
  li .x5 1,.ite (.ltu .x22 .x5) (seq [li .x24 1,success .x24 .x23]) empty,
  li .x5 3,.ite (.geu .x22 .x5) (seq [li .x24 1,success .x24 .x23]) empty,
  get .x5 20,li .x6 1,
  .ite (.eq .x5 .x6) (.ite (.ne .x22 .x6) (seq [li .x24 1,success .x24 .x23]) empty) empty,
  sourceSlot false,ins [.LD .x28 .x26 0,.LD .x29 .x26 16,
    .SD .x20 .x23 0,.SD .x20 .x28 8,.SD .x20 .x29 16,.SD .x20 .x22 24],
  releaseQuotaCore,li .x24 2,success .x24 .x23]

end Libp2pAsm.Asm.Kernel
