import Libp2pAsm.Asm.Kernel.Common

namespace Libp2pAsm.Asm.Kernel
open Rv64

/-- Header 256; 128-byte slots; private payloads follow slots for non-timers only.
Header fields: total, reserved, nextID, completionCap, four kind caps, four used,
stride, maxActions, actionsUsed, unused, cleanupMode, cleanupCursor,
three request timeouts, unused, readyCursor. -/
def requestSlot : SAsm.Stmt := seq [input .x24 0,get .x25 0,reject (.geu .x24 .x25) 13,
  ins [.SLLI .x26 .x24 7,.ADD .x26 .x8 .x26,.ADDI .x26 .x26 256],
  input .x24 1,ins [.LD .x25 .x26 0],reject (.ne .x24 .x25) 14]

def requestPayload : SAsm.Stmt := seq [get .x24 0,get .x25 12,
  ins [.SLLI .x24 .x24 7,.ADD .x27 .x8 .x24,.ADDI .x27 .x27 256],
  ins [.SUB .x24 .x26 .x8,.ADDI .x24 .x24 (-256),.SRLI .x24 .x24 7,
    .MUL .x24 .x24 .x25,.ADD .x27 .x27 .x24]]

def wipePayload : SAsm.Stmt := seq [ins [.LD .x5 .x26 24],li .x6 3,
  .ite (.ne .x5 .x6) (seq [requestPayload,get .x28 12,
    .loop (.ne .x28 .x0) (ins [.SB .x27 .x0 0,.ADDI .x27 .x27 1,.ADDI .x28 .x28 (-1)])]) empty]

def issueChecks : SAsm.Stmt := seq [get .x5 16,reject (.ne .x5 .x0) 15,requestSlot,
  ins [.LD .x5 .x26 8],li .x6 4,reject (.eq .x5 .x6) 16,reject (.ne .x5 .x0) 15,
  input .x22 2,li .x5 3,reject (.ltu .x5 .x22) 12,
  get .x24 0,get .x25 7,ins [.SUB .x24 .x24 .x25],input .x25 0,
  .ite (.eq .x22 .x5) (reject (.ltu .x25 .x24) 13) (reject (.geu .x25 .x24) 13),
  ins [.SLLI .x5 .x22 3,.ADD .x28 .x8 .x5,.LD .x24 .x28 32,.LD .x25 .x28 64],
  reject (.geu .x25 .x24) 19,get .x24 1,get .x25 3,reject (.geu .x24 .x25) 19,
  get .x24 14,get .x25 13,reject (.geu .x24 .x25) 19,
  get .x24 2,reject (.eq .x24 .x0) 17,
  input .x24 5,get .x25 12,reject (.ltu .x25 .x24) 13,
  li .x5 3,.ite (.eq .x22 .x5) (reject (.ne .x24 .x0) 13) empty,
  input .x24 8,li .x25 1,reject (.ltu .x25 .x24) 12]

def requestIssue : SAsm.Stmt := seq [enter 256 88 128,issueChecks,
  input .x24 3,input .x25 4,li .x5 3,
  .ite (.ne .x22 .x5) (seq [ins [.SLLI .x5 .x22 3,.ADD .x5 .x8 .x5,.LD .x25 .x5 144]]) empty,
  reject (.eq .x25 .x0) 13,addChecked .x29 .x24 .x25 17,
  li .x5 1,ins [.SD .x26 .x5 8],get .x24 2,ins [.SD .x26 .x24 16,.SD .x26 .x22 24,.SD .x26 .x29 32],
  seq ([5,6,7,8,9,10].zipIdx.map fun (i,j) => seq [input .x24 i,ins [.SD .x26 .x24 (imm (40+j*8))]]),
  ins [.SD .x26 .x0 88,.SD .x26 .x0 96,.SD .x26 .x0 104,.SD .x26 .x0 112,.SD .x26 .x0 120],
  get .x24 2,ins [.ADDI .x25 .x0 (-1)],
  .ite (.eq .x24 .x25) (putN 2 0) (seq [ins [.ADDI .x24 .x24 1],put 2 .x24]),
  get .x24 1,ins [.ADDI .x24 .x24 1],put 1 .x24,
  get .x24 14,ins [.ADDI .x24 .x24 1],put 14 .x24,
  ins [.LD .x24 .x28 64,.ADDI .x24 .x24 1,.SD .x28 .x24 64],
  seq ((List.range 16).map fun i => ins [.LD .x5 .x26 (imm (i*8)),.SD .x20 .x5 (imm (i*8))]),
  ins [.LD .x24 .x26 16,.LD .x25 .x26 32],success .x24 .x25]

/-- Matching is before mutation. Invalid length/failure/late response is a completed
aborted request, not an accepted random/clock value. Only trusted host envelope 2. -/
def requestComplete : SAsm.Stmt := seq [enter 256 56 0,li .x5 2,reject (.ne .x22 .x5) 23,
  requestSlot,ins [.LD .x5 .x26 8],li .x6 1,reject (.ne .x5 .x6) 14,
  input .x24 2,ins [.LD .x25 .x26 16],reject (.ne .x24 .x25) 14,
  input .x24 3,ins [.LD .x25 .x26 24],reject (.ne .x24 .x25) 14,
  input .x29 4,ins [.LD .x24 .x26 32],li .x23 0,li .x5 3,
  .ite (.eq .x25 .x5) (reject (.ltu .x29 .x24) 25)
    (.ite (.geu .x29 .x24) (li .x23 4) empty),
  input .x24 5,li .x5 3,reject (.ltu .x5 .x24) 12,
  .ite (.ne .x24 .x0) (.ite (.eq .x23 .x0) (mov .x23 .x24) empty) empty,
  input .x24 6,ins [.ADDI .x5 .x19 (-56)],
  .ite (.ne .x24 .x5) (li .x23 6) empty,
  ins [.LD .x5 .x26 40],.ite (.ne .x24 .x5) (li .x23 6) empty,
  wipePayload,
  .ite (.eq .x23 .x0) (seq [ins [.LD .x5 .x26 24],li .x6 3,
    .ite (.ne .x5 .x6) (seq [requestPayload,input .x28 6,ins [.ADDI .x25 .x18 56],
      .loop (.ne .x28 .x0) (ins [.LBU .x5 .x25 0,.SB .x27 .x5 0,
        .ADDI .x25 .x25 1,.ADDI .x27 .x27 1,.ADDI .x28 .x28 (-1)])]) empty]) empty,
  li .x5 2,ins [.SD .x26 .x5 8,.SD .x26 .x23 112,.SD .x26 .x29 120],success .x23 .x0]

def reapBody : SAsm.Stmt := seq [get .x24 12,li .x25 128,addChecked .x24 .x24 .x25 17,
  reject (.ltu .x21 .x24) 11,
  seq ((List.range 16).map fun i => ins [.LD .x5 .x26 (imm (i*8)),.SD .x20 .x5 (imm (i*8))]),
  ins [.LD .x23 .x26 112,.LD .x22 .x26 16],
  ins [.LD .x5 .x26 24],li .x6 3,
  .ite (.ne .x5 .x6) (seq [requestPayload,get .x28 12,ins [.ADDI .x25 .x20 128],
    .loop (.ne .x28 .x0) (ins [.LBU .x5 .x27 0,.SB .x25 .x5 0,.SB .x27 .x0 0,
      .ADDI .x25 .x25 1,.ADDI .x27 .x27 1,.ADDI .x28 .x28 (-1)])]) empty,
  ins [.LD .x24 .x26 24,.SLLI .x24 .x24 3,.ADD .x24 .x8 .x24,
    .LD .x25 .x24 64,.ADDI .x25 .x25 (-1),.SD .x24 .x25 64],
  get .x24 1,ins [.ADDI .x24 .x24 (-1)],put 1 .x24,
  ins [.LD .x24 .x26 0,.ADDI .x25 .x0 (-1)],
  .ite (.eq .x24 .x25) (seq [li .x5 4,ins [.SD .x26 .x5 8]])
    (ins [.ADDI .x24 .x24 1,.SD .x26 .x24 0,.SD .x26 .x0 8]),
  ins ((List.range 14).map fun i => .SD .x26 .x0 (imm (16+i*8))),success .x22 .x23]

def requestReap : SAsm.Stmt := seq [enter 256 16 128,requestSlot,
  ins [.LD .x5 .x26 8],li .x6 2,reject (.ne .x5 .x6) 14,reapBody]

/-- One row per call. No TLS transition is performed; canceled owned resources remain
reserved, queued in their own slots until the caller consumes/reaps the outcome. -/
def requestCleanup : SAsm.Stmt := seq [enter 256 0 0,get .x24 16,
  .ite (.eq .x24 .x0) (seq [li .x5 1,reject (.ltu .x22 .x5) 12,li .x5 2,
    reject (.ltu .x5 .x22) 12,put 16 .x22,putN 17 0]) empty,
  get .x22 17,get .x23 0,
  .ite (.geu .x22 .x23) (seq [putN 16 0,putN 17 0,success .x0 .x0]) empty,
  ins [.SLLI .x26 .x22 7,.ADD .x26 .x8 .x26,.ADDI .x26 .x26 256],
  ins [.LD .x5 .x26 8],li .x6 3,
  .ite (.ne .x5 .x0) (.ite (.ltu .x5 .x6) (seq [get .x5 16,li .x6 2,ins [.LD .x7 .x26 64],
    .ite (.eq .x5 .x6) (li .x7 1) empty,
    .ite (.ne .x7 .x0) (seq [wipePayload,li .x5 2,li .x6 5,
      ins [.SD .x26 .x5 8,.SD .x26 .x6 112]]) empty]) empty) empty,
  ins [.ADDI .x22 .x22 1],put 17 .x22,li .x24 1,success .x24 .x22]

def requestStop (expiry : Bool) : SAsm.Stmt := seq [enter 256 (if expiry then 32 else 24) 0,
  requestSlot,ins [.LD .x5 .x26 8],li .x6 1,reject (.ne .x5 .x6) 14,
  input .x24 2,ins [.LD .x25 .x26 16],reject (.ne .x24 .x25) 14,
  if expiry then seq [input .x24 3,ins [.LD .x25 .x26 32],reject (.ltu .x24 .x25) 25] else empty,
  wipePayload,li .x23 (if expiry then 4 else 5),
  if expiry then seq [ins [.LD .x5 .x26 24],li .x6 3,
    .ite (.eq .x5 .x6) (li .x23 0) empty] else empty,
  li .x5 2,ins [.SD .x26 .x5 8,.SD .x26 .x23 112],success .x23 .x0]

/-- Bounded round-robin readiness discovery. first=slot+1 on ready; zero means
this slice found none, second=next owned cursor. It does not consume a completion. -/
def requestNext : SAsm.Stmt := seq [enter 256 0 0,get .x22 22,get .x23 0,li .x27 32,
  .loop (.ne .x27 .x0) (seq [
    ins [.SLLI .x26 .x22 7,.ADD .x26 .x8 .x26,.ADDI .x26 .x26 256,
      .LD .x5 .x26 8,.ADDI .x24 .x22 1,.REMU .x22 .x24 .x23],put 22 .x22,
    li .x6 2,.ite (.eq .x5 .x6) (success .x24 .x22) empty,
    ins [.ADDI .x27 .x27 (-1)]]),success .x0 .x22]

/-- One deadline slot per visit, independently of host completion delivery. -/
def requestExpireNext : SAsm.Stmt := seq [enter 256 8 0,get .x22 23,get .x25 0,input .x23 0,
  ins [.SLLI .x26 .x22 7,.ADD .x26 .x8 .x26,.ADDI .x26 .x26 256,
    .ADDI .x24 .x22 1,.REMU .x24 .x24 .x25],put 23 .x24,
  ins [.LD .x5 .x26 8],li .x6 1,
  .ite (.ne .x5 .x6) (success .x0 .x22) empty,
  ins [.LD .x5 .x26 32],.ite (.ltu .x23 .x5) (success .x0 .x22) empty,
  wipePayload,li .x29 4,ins [.LD .x5 .x26 24],li .x6 3,
  .ite (.eq .x5 .x6) (li .x29 0) empty,
  li .x5 2,ins [.SD .x26 .x5 8,.SD .x26 .x29 112,.SD .x26 .x23 120,.ADDI .x22 .x22 1],
  success .x22 .x29]

end Libp2pAsm.Asm.Kernel
