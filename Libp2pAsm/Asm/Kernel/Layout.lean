import Libp2pAsm.Asm.Kernel.Limits

namespace Libp2pAsm.Asm.Kernel
open Rv64

private def reqCount : Amount := .add (.field 30) (.add (.field 32) (.field 33))
private def totalCount : Amount := .add reqCount (.field 31)

def areaSizes : List Amount :=
  [.add (.literal 128) (.mul (.literal 64) (.field 60)),
   .add (.add (.literal 256) (.mul (.literal 128) totalCount))
      (.mul (.align (.field 10) 8) reqCount),
   .add (.literal 256) (.mul (.literal 128) (.field 4)),
   .add (.literal 128) (.mul (.literal 64) (.field 0)),
   .add (.literal 64) (.mul (.literal 256) (.field 34)),
   .add (.literal 64) (.mul (.literal 256) (.field 35)),.literal 192]

def areaOffsets : List Amount := areaSizes.foldl (fun xs n => xs ++ [.add xs.getLast! n]) [.literal 1024]

def connectionArea : Amount := .mul (.field 0)
  (.add (.add (.add (.field 56) (.field 57)) (.mul (.literal 2) (.field 19)))
    (.mul (.field 16) (.add (.field 17) (.field 18))))
def datagramStart : Amount := .add (.field 58) connectionArea

def eventStart : Amount := .align (.add datagramStart (.mul (.add (.field 15) (.field 30)) (.field 10))) 16

def stackStart : Amount := .add eventStart (.mul (.field 27) (.literal 256))
def usedBytes : Amount := .add stackStart (.field 59)
def directory : List Amount := areaOffsets.take 7 ++ [.field 58,datagramStart,eventStart,stackStart,usedBytes]

/-- Begin on caller-owned uninitialized mapped arena. No publication on policy/layout
failure. All table capacities come from the sole raw Limits input. -/
def initBegin : SAsm.Stmt := seq [enter 1024 0 0,validateLimitsBody,
  amount areaOffsets.getLast! 22,input .x25 58,reject (.ltu .x25 .x24) 22,
  ins [.ANDI .x5 .x25 15],reject (.ne .x5 .x0) 22,
  amount usedBytes 22,input .x25 55,reject (.ltu .x25 .x24) 22,reject (.ltu .x9 .x24) 22,
  input .x25 51,li .x7 1000000,reject (.ltu .x25 .x7) 22,
  ins [.ANDI .x5 .x8 15],reject (.ne .x5 .x0) 10,
  ins [.ADD .x5 .x22 .x23],reject (.ltu .x5 .x22) 9,
  .ite (.ltu .x8 .x22) (seq [ins [.SUB .x5 .x22 .x8],reject (.ltu .x5 .x9) 18])
    (seq [ins [.SUB .x5 .x8 .x22],reject (.ltu .x5 .x23) 18]),
  mov .x26 .x8,li .x27 128,
  .loop (.ne .x27 .x0) (ins [.SD .x26 .x0 0,.ADDI .x26 .x26 8,.ADDI .x27 .x27 (-1)]),
  putN 0 1,put 1 .x24,putN 2 1024,put 4 .x9,put 5 .x22,put 6 .x23,
  seq (directory.zipIdx.map fun (e,i) => seq [amount e 22,put (8+i) .x24]),
  amount areaOffsets.getLast! 22,put 3 .x24,
  mov .x26 .x18,ins [.ADDI .x27 .x8 512],li .x28 488,
  .loop (.ne .x28 .x0) (ins [.LBU .x5 .x26 0,.SB .x27 .x5 0,
    .ADDI .x26 .x26 1,.ADDI .x27 .x27 1,.ADDI .x28 .x28 (-1)]),
  li .x24 1,li .x25 1024,success .x24 .x25]

private def policy (dst : Reg) (i : Nat) : SAsm.Stmt := get dst (64+i)
private def table (i : Nat) : SAsm.Stmt := seq [get .x26 (8+i),ins [.ADD .x26 .x8 .x26]]
private def field (off policyIndex : Nat) : SAsm.Stmt := seq [policy .x24 policyIndex,ins [.SD .x26 .x24 (imm (off*8))]]

private def initHeaders : SAsm.Stmt := seq [
  table 0,field 0 60,ins [.SD .x26 .x8 32],get .x24 1,ins [.SD .x26 .x24 40],
  get .x24 5,get .x25 6,ins [.SD .x26 .x24 48,.SD .x26 .x25 56],
  table 1,policy .x24 30,policy .x25 32,policy .x28 33,policy .x29 31,
  ins [.ADD .x24 .x24 .x25,.ADD .x24 .x24 .x28,.ADD .x24 .x24 .x29,.SD .x26 .x24 0],
  li .x24 1,ins [.SD .x26 .x24 16],field 3 28,
  field 4 30,field 5 32,field 6 33,field 7 31,
  policy .x24 10,ins [.ADDI .x24 .x24 7,.ANDI .x24 .x24 (-8),.SD .x26 .x24 96],
  field 13 35,field 18 38,field 19 40,field 20 41,
  table 2,field 0 4,field 8 13,field 9 14,field 10 12,field 11 11,
  field 16 2,field 17 3,field 18 5,field 19 6,field 20 7,field 23 0,field 24 1,field 28 10,
  policy .x24 13,policy .x25 4,ins [.DIVU .x24 .x24 .x25],
  .ite (.eq .x24 .x0) (li .x24 1) empty,ins [.SD .x26 .x24 200],
  policy .x24 14,ins [.DIVU .x24 .x24 .x25],policy .x25 10,
  .ite (.ltu .x24 .x25) (mov .x24 .x25) empty,ins [.SD .x26 .x24 208],
  table 3,field 0 0,field 4 54,field 5 51,field 6 52,field 7 53,field 8 35,
  table 4,field 0 34,li .x24 3,ins [.SD .x26 .x24 32],li .x24 64,ins [.SD .x26 .x24 40],
  table 5,field 0 35,li .x24 4,ins [.SD .x26 .x24 32],li .x24 64,ins [.SD .x26 .x24 40],
  table 6,get .x28 17,ins [.ADD .x28 .x8 .x28],
  field 0 15,ins [.SUB .x24 .x28 .x26,.SD .x26 .x24 40],policy .x24 15,
  ins [.SLLI .x24 .x24 8,.ADD .x28 .x28 .x24,.ADDI .x26 .x26 64],
  field 0 29,li .x24 1,ins [.SD .x26 .x24 32,.SUB .x24 .x28 .x26,.SD .x26 .x24 40],policy .x24 29,
  ins [.SLLI .x24 .x24 8,.ADD .x28 .x28 .x24,.ADDI .x26 .x26 64],
  field 0 28,li .x24 2,ins [.SD .x26 .x24 32,.SUB .x24 .x28 .x26,.SD .x26 .x24 40]]

/-- At most 4096 bytes cleared per call, followed by constant-size header setup.
Only the last call publishes ready=2. The cursor is core-owned and cannot be supplied by an event. -/
def initResume : SAsm.Stmt := seq [enter 1024 0 0,get .x24 0,li .x25 1,reject (.ne .x24 .x25) 14,
  get .x22 2,get .x23 1,li .x27 4096,
  .loop (.ltu .x22 .x23) (seq [
    .ite (.eq .x27 .x0) (seq [put 2 .x22,li .x24 1,success .x24 .x22]) empty,
    ins [.ADD .x26 .x8 .x22,.SB .x26 .x0 0,.ADDI .x22 .x22 1,.ADDI .x27 .x27 (-1)]]),
  put 2 .x22,initHeaders,putN 0 2,success .x0 .x22]

end Libp2pAsm.Asm.Kernel
