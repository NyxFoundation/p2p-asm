import Libp2pAsm.Asm.Kernel.Registry
import Libp2pAsm.Asm.Kernel.Requests
import Libp2pAsm.Asm.Crypto.Link

namespace Libp2pAsm.Asm.Kernel
open Rv64 Crypto.Link

private def asm (s : SAsm.Stmt) : Part := .asm s
private def parts (xs : List Part) : Part := .seq xs

/-- The original frozen resolver is called unchanged. Resolution additionally requires
an outstanding matching read/send or write lease in the core-owned borrow side table. -/
def resolveRegistered : Except String SAsm.Stmt :=
  Crypto.Link.program (parts [asm (enter 128 32 0),
    asm (seq [seq ((List.range 4).map fun i => seq [input .x5 i,ins [.SD .x2 .x5 (imm (128+i*8))]]),
      ins [.ADDI .x10 .x8 128,.ADDI .x11 .x2 128],get .x12 0,mov .x13 .x22]),.call 0,
    .ite (.ne .x10 .x0) (asm leave) (parts [
      asm (seq [mov .x24 .x11,mov .x25 .x12,input .x5 0,get .x6 0,
        ins [.ADD .x5 .x5 .x6,.SLLI .x5 .x5 5,.ADD .x26 .x8 .x5,.ADDI .x26 .x26 128]]),
      .ite (.eq .x22 .x0)
        (asm (seq [ins [.LD .x5 .x26 0,.LD .x6 .x26 8,.OR .x5 .x5 .x6],reject (.eq .x5 .x0) 15]))
        (asm (seq [ins [.LD .x5 .x26 16],li .x6 1,reject (.ne .x5 .x6) 15])),
      asm (success .x24 .x25)])]) [asm Asm.resolveBuffer]

/-- Set up an internal leaf's span from validated init directory entries.
The whole arena remains owned by the root caller; subtable footprints are narrower. -/
private def subtable (index : Nat) : SAsm.Stmt := seq [
  get .x10 index,get .x11 (index+1),ins [.SUB .x11 .x11 .x10,.ADD .x10 .x8 .x10],
  mov .x14 .x20,mov .x15 .x21,li .x16 0,li .x17 0]

private def registryArgs (response : Bool) : SAsm.Stmt := seq [subtable 8,
  ins [.ADDI .x12 (if response then .x20 else .x18) 72],li .x13 16,li .x15 0]
private def requestArgs : SAsm.Stmt := seq [subtable 9,mov .x12 .x18,mov .x13 .x19]
private def nestedEnter (inputMin : Nat) : SAsm.Stmt := seq [
  li .x7 512,earlyReject (.ltu .x2 .x7) 9,ins [.ADDI .x28 .x2 (-512)],
  apart .x28 .x7 .x10 .x11,apart .x28 .x7 .x12 .x13,apart .x28 .x7 .x14 .x15,
  enter 160 inputMin 128]

private def saveResult : SAsm.Stmt := ins [.ADDI .x24 .x10 0,.ADDI .x25 .x11 0,.ADDI .x26 .x12 0]
private def restoreResult : SAsm.Stmt := seq [mov .x10 .x24,mov .x11 .x25,mov .x12 .x26,leave]

/-- Atomic resource issue: reserve immutable registry send lease, then completion slot
and action. Failed request issuance rolls the newly acquired lease back. No packet
number or recovery transition is implemented here. Nested stack extent is 512 bytes. -/
def issueOwned : Except String SAsm.Stmt :=
  Crypto.Link.program (parts [asm (nestedEnter 88),
    asm (seq [get .x5 0,li .x6 2,reject (.ne .x5 .x6) 14,input .x22 2]),
    .ite (.eq .x22 .x0) (parts [asm (registryArgs false),.call 0,
      .ite (.ne .x10 .x0) (asm leave) (asm empty)]) (asm empty),
    asm requestArgs,.call 1,asm saveResult,
    .ite (.ne .x24 .x0) (.ite (.eq .x22 .x0)
      (parts [asm (registryArgs false),.call 2]) (asm empty)) (asm empty),
    asm restoreResult]) [asm (registryMutation 5),asm requestIssue,asm (registryMutation 6)]

/-- Consume the completion once and then release its send lease. Structural ownership
requires a live lease for every unreaped send row. Host fields cannot manufacture it. -/
def reapOwned : Except String SAsm.Stmt :=
  Crypto.Link.program (parts [asm (nestedEnter 16),
    asm (seq [get .x5 0,li .x6 2,reject (.ne .x5 .x6) 14,requestArgs]),
    .call 0,asm saveResult,
    .ite (.eq .x24 .x0) (parts [asm (ins [.LD .x5 .x20 24]),
      .ite (.eq .x5 .x0) (parts [asm (registryArgs true),.call 1]) (asm empty)]) (asm empty),
    asm restoreResult]) [asm requestReap,asm (registryMutation 6)]

/-- Copy a complete borrowed view into caller-owned private storage. At most 65536
bytes are copied per call; larger views fail before writes and must not survive step
return as host references. This is an implementation charge bound, not configuration. -/
def copyRegistered : Except String SAsm.Stmt :=
  Crypto.Link.program (parts [asm (enter 128 32 0),
    asm (seq [seq ((List.range 4).map fun i => seq [input .x5 i,ins [.SD .x2 .x5 (imm (128+i*8))]]),
      ins [.ADDI .x10 .x8 128,.ADDI .x11 .x2 128],get .x12 0,li .x13 0]),.call 0,
    .ite (.ne .x10 .x0) (asm leave) (parts [asm (seq [
      mov .x24 .x11,mov .x25 .x12,input .x5 0,get .x6 0,
      ins [.ADD .x5 .x5 .x6,.SLLI .x5 .x5 5,.ADD .x26 .x8 .x5,.ADDI .x26 .x26 128,
        .LD .x5 .x26 0,.LD .x6 .x26 8,.OR .x5 .x5 .x6],reject (.eq .x5 .x0) 15,
      reject (.ltu .x21 .x25) 11,li .x5 65536,reject (.ltu .x5 .x25) 19,
      .ite (.ne .x25 .x0) (checkDisjoint .x24 .x25 .x20 .x21) empty,
      mov .x26 .x24,mov .x27 .x20,mov .x28 .x25,
      .loop (.ne .x28 .x0) (ins [.LBU .x5 .x26 0,.SB .x27 .x5 0,
        .ADDI .x26 .x26 1,.ADDI .x27 .x27 1,.ADDI .x28 .x28 (-1)]),success .x25 .x0])])])
    [asm Asm.resolveBuffer]

/-- Core scheduler entry. Finish the bounded input-borrow drain before returning
host memory or starting another quantum. Completion and timer visits remain available
when UDP admission refuses input. -/
def kernelQuantum : SAsm.Stmt := seq [enter 160 0 0,get .x5 0,li .x6 2,reject (.ne .x5 .x6) 14,
  get .x24 8,ins [.ADD .x24 .x8 .x24,.LD .x5 .x24 16],reject (.ne .x5 .x0) 15,
  ins [.LD .x5 .x24 120],reject (.ne .x5 .x0) 15,
  get .x24 9,ins [.ADD .x24 .x8 .x24,.SD .x24 .x0 112],
  get .x24 10,ins [.ADD .x24 .x8 .x24,.SD .x24 .x0 56],
  get .x24 11,ins [.ADD .x24 .x8 .x24,.LD .x25 .x24 80,.LD .x26 .x24 0],
  get .x28 22,li .x5 2,
  .ite (.eq .x28 .x5) (ins [.ADDI .x27 .x25 1,.REMU .x27 .x27 .x26,.SD .x24 .x27 80]) empty,
  ins [.SD .x24 .x0 24,.SD .x24 .x0 72,.ADDI .x27 .x28 1],li .x5 5,
  ins [.REMU .x27 .x27 .x5],put 22 .x27,success .x25 .x28]

end Libp2pAsm.Asm.Kernel
