import Libp2pAsm.Asm.Kernel.Common

namespace Libp2pAsm.Asm.Kernel
open Rv64

def queueRoom (drop : Bool := false) : SAsm.Stmt := seq [
  get .x24 2,get .x25 3,ins [.ADD .x24 .x24 .x25],get .x25 0,
  reject (.geu .x24 .x25) (if drop then 20 else 19)]

def queueReserve (cancel : Bool) : SAsm.Stmt := seq [enter 64 0 0,
  if cancel then seq [get .x24 3,reject (.eq .x24 .x0) 14,ins [.ADDI .x24 .x24 (-1)]]
  else seq [queueRoom,get .x24 3,ins [.ADDI .x24 .x24 1]],
  put 3 .x24,success .x0 .x0]

def queueEnqueue (completion : Bool) : SAsm.Stmt := seq [enter 64 0 0,
  get .x24 4,reject (.ne .x24 .x22) 23,li .x25 4,reject (.ltu .x25 .x22) 23,
  li .x24 224,reject (.ltu .x24 .x19) 13,
  if completion then seq [li .x24 2,reject (.ne .x22 .x24) 23,
    get .x24 3,reject (.eq .x24 .x0) 14]
  else .ite (.eq .x22 .x0) (queueRoom true) queueRoom,
  get .x24 1,get .x25 2,get .x26 0,
  ins [.ADD .x24 .x24 .x25,.REMU .x24 .x24 .x26,.SLLI .x24 .x24 8,
    .ADD .x24 .x8 .x24,.LD .x5 .x8 40,.ADD .x24 .x24 .x5],
  mov .x26 .x24,li .x27 32,
  .loop (.ne .x27 .x0) (ins [.SD .x26 .x0 0,.ADDI .x26 .x26 8,.ADDI .x27 .x27 (-1)]),
  ins [.SD .x24 .x22 0,.SD .x24 .x19 8,.ADDI .x26 .x24 32],mov .x27 .x18,mov .x28 .x19,
  .loop (.ne .x28 .x0) (ins [.LBU .x5 .x27 0,.SB .x26 .x5 0,
    .ADDI .x27 .x27 1,.ADDI .x26 .x26 1,.ADDI .x28 .x28 (-1)]),
  get .x24 2,ins [.ADDI .x24 .x24 1],put 2 .x24,
  if completion then seq [get .x24 3,ins [.ADDI .x24 .x24 (-1)],put 3 .x24] else empty,
  success .x0 .x0]

def queueDequeue : SAsm.Stmt := seq [enter 64 0 256,get .x24 2,reject (.eq .x24 .x0) 19,
  get .x24 1,ins [.SLLI .x25 .x24 8,.ADD .x25 .x8 .x25,.LD .x5 .x8 40,.ADD .x25 .x25 .x5],
  ins [.LD .x28 .x25 0,.LD .x29 .x25 8],mov .x26 .x20,li .x27 32,
  .loop (.ne .x27 .x0) (ins [.LD .x5 .x25 0,.SD .x26 .x5 0,.SD .x25 .x0 0,
    .ADDI .x25 .x25 8,.ADDI .x26 .x26 8,.ADDI .x27 .x27 (-1)]),
  get .x25 0,ins [.ADDI .x24 .x24 1,.REMU .x24 .x24 .x25],put 1 .x24,
  get .x24 2,ins [.ADDI .x24 .x24 (-1)],put 2 .x24,success .x28 .x29]

end Libp2pAsm.Asm.Kernel
