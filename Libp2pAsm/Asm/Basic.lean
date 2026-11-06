import Libp2pAsm.Rv64.SAsm

namespace Libp2pAsm.Asm

open Rv64

def sequence (items : List SAsm.Stmt) : SAsm.Stmt :=
  items.foldr .seq (.block [])

/-- Return a status and two zeroed result registers; no memory is written. -/
def returnError (code : BitVec 12) : SAsm.Stmt :=
  .seq (.block [.ADDI .x10 .x0 code, .ADDI .x11 .x0 0, .ADDI .x12 .x0 0]) .ret

def rejectIf (condition : SAsm.Cond) (code : BitVec 12) : SAsm.Stmt :=
  .ite condition (returnError code) (.block [])

end Libp2pAsm.Asm
