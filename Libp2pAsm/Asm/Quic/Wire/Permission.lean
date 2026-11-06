import Libp2pAsm.Asm.Quic.Wire.Common

namespace Libp2pAsm.Asm.Quic.Wire
open Rv64 Crypto.Util

private def tiny (r : Reg) (n : Nat) : SAsm.Stmt := .block [.ADDI r .x0 (imm n)]
private def noop : SAsm.Stmt := .block []
private def deny (status : Nat) : SAsm.Stmt := sequence [
  .block ([.ADDI .x10 .x0 (imm status)] ++
    ((Crypto.Sha2.cleared.filter (· != .x10)).map fun r => .ADDI r .x0 0)),.ret]
private def denyIf (c : SAsm.Cond) (status : Nat) : SAsm.Stmt := .ite c (deny status) noop

private def permittedReturn : SAsm.Stmt := sequence [tiny .x12 1,
  sequence ([2,3,28,29].map fun n => sequence [tiny .x7 n,.ite (.eq .x10 .x7) (tiny .x12 0) noop]),
  .block [.ADDI .x11 .x12 0],.ite (.eq .x10 .x0) (tiny .x11 0) noop,
  tiny .x10 0,
  .block ((Crypto.Sha2.cleared.filter fun r => r != .x10 && r != .x11 && r != .x12).map
    fun r => .ADDI r .x0 0),.ret]

private def permissionBody : SAsm.Stmt := sequence [tiny .x7 31,denyIf (.geu .x10 .x7) 7,
  tiny .x7 4,denyIf (.geu .x11 .x7) 10,tiny .x7 2,denyIf (.geu .x12 .x7) 10,
  .ite (.eq .x12 .x0) (sequence ([7,30].map fun n => sequence [tiny .x7 n,
    denyIf (.eq .x10 .x7) 9])) noop,
  tiny .x7 2,.ite (.geu .x11 .x7) noop (sequence [
    sequence ([0,1,2,3,6,28].map fun n => sequence [tiny .x7 n,
      .ite (.eq .x10 .x7) permittedReturn noop]),deny 9]),
  tiny .x7 2,.ite (.eq .x11 .x7) (sequence [denyIf (.ne .x12 .x0) 9,
    sequence ([2,3,6,7,25,27,30].map fun n => sequence [tiny .x7 n,
      denyIf (.eq .x10 .x7) 9])]) noop,permittedReturn]

/-- a0=type,a1=level (Initial=0,Handshake=1,0RTT=2,1RTT=3),a2=sender role.
Returns status/ack-eliciting/in-flight flags in a0/a1/a2; no memory or stack accesses. -/
def framePermission : Except String SAsm.Stmt :=
  permissionBody.validate.mapError (fun e => s!"wire permission lowering: {repr e}") *> pure permissionBody

end Libp2pAsm.Asm.Quic.Wire
