import Libp2pAsm.Asm.Kernel.Common

namespace Libp2pAsm.Asm.Kernel
open Rv64

/-- a0=generation -> a0=nonwrapping next, a1=permanent retirement bit.
This exact block is shared with registry release; it never emits a wrapped generation. -/
def generationCode : List Instr := [
  .ADDI .x5 .x0 (-1),.SLTU .x6 .x10 .x5,.ADD .x10 .x10 .x6,.XORI .x11 .x6 1]

def nextGeneration : SAsm.Stmt := seq [ins generationCode,
  ins ([.ADDI .x12 .x0 0] ++ clear),.ret]

end Libp2pAsm.Asm.Kernel
