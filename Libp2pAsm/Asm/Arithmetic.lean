import Libp2pAsm.Rv64.SAsm

namespace Libp2pAsm.Asm

open Rv64

/-- LP64 leaf: a0 := a0 + a1 modulo 2^64; preserve all other registers. -/
def addWords : SAsm.Stmt :=
  .seq (.block [.ADD .x10 .x10 .x11]) .ret

/-- LP64 leaf: a0 := min(a0, a1), with unsigned operands. -/
def minWords : SAsm.Stmt :=
  .seq (.ite (.ltu .x10 .x11) (.block []) (.block [.ADDI .x10 .x11 0])) .ret

end Libp2pAsm.Asm
