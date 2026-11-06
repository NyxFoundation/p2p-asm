import Libp2pAsm.Asm.Stream.Common

namespace Libp2pAsm.Asm.Stream
open Rv64 Crypto.Util

/-- The actual bit extraction block used by validateId. -/
def idParts : List Instr := [.ANDI .x11 .x10 1, .SRLI .x12 .x10 1,
  .ANDI .x12 .x12 1, .SRLI .x13 .x10 2]

/-- No allocation. a0=id, a1=local role (client0/server1), a2=maximum stream
count, a3=0 receive/1 send. Caller validates registry and implicitly opened IDs.
Returns initiator/direction/ordinal/localInitiated in a1..a4. -/
def validateId : SAsm.Stmt := seq [
  b [.ADDI .x5 .x0 1], guard (.ltu .x5 .x11) 1 false,
  guard (.ltu .x5 .x13) 1 false,
  b [.SRLI .x5 .x10 62], guard (.ne .x5 .x0) 2 false,
  b [.ADDI .x5 .x0 1, .SLLI .x5 .x5 60], guard (.ltu .x5 .x12) 15 false,
  b [.ADDI .x28 .x11 0, .ADDI .x29 .x13 0, .ADDI .x30 .x12 0],
  b idParts, guard (.geu .x13 .x30) 15 false,
  b [.XOR .x14 .x11 .x28, .XORI .x14 .x14 1],
  .ite (.ne .x12 .x0) (guard (.ne .x14 .x29) 16 false) nil,
  b [.ADDI .x10 .x0 0], exit false]

/-- Minimal actual leaf for correspondence proof. Precondition: id is a u62.
Returns its stream ordinal in a0, zeroes all other caller-saved registers. -/
def ordinal : SAsm.Stmt := seq [b [.SRLI .x10 .x10 2, .ADDI .x11 .x0 0,
  .ADDI .x12 .x0 0, .ADDI .x13 .x0 0, .ADDI .x14 .x0 0], exit false]

end Libp2pAsm.Asm.Stream
