import Libp2pAsm.Asm.Crypto.Util

namespace Libp2pAsm.Asm.Identity.Certificate
open Rv64

/-- Actual arithmetic leaf in authentication: t0=parsed usage,t1=validated role.
The owning routine rejects a zero result before any identity publication. -/
def usageInstruction : Instr := .AND .x5 .x5 .x6
def usageMask : SAsm.Stmt := .block [usageInstruction]

end Libp2pAsm.Asm.Identity.Certificate
