import Libp2pAsm.Asm.Crypto.Curve25519.Edwards

namespace Libp2pAsm.Asm.Crypto.Curve25519.Verify
open Rv64 Util Link Edwards

private def failIf (c : SAsm.Cond) (status : Nat) : Part :=
  .ite c (finishOwned status) (.asm empty)

private def scalarCanonical : Part := .seq [
  .asm (block (ptr .x10 .x19 1824 ++ [.ADDI .x11 .x20 32, .ADDI .x12 .x0 32])),
  .asm (copy .x10 .x11 .x12), reduce 1664 1824 32,
  .asm (block <| [.ADDI .x28 .x0 0] ++ ((List.range 4).flatMap fun i =>
    [.LD .x5 .x19 (imm (1664+8*i)), .LD .x6 .x19 (imm (1824+8*i)),
     .XOR .x5 .x5 .x6, .OR .x28 .x28 .x5])), failIf (.ne .x28 .x0) 10]

private def decode (out : Nat) (input : Reg) : Part := .seq [
  .asm (block (ptr .x10 .x19 out ++ [.ADDI .x11 input 0] ++ ptr .x12 .x19 3080)),
  .call 10, failIf (.ne .x10 .x0) 10]

/-- x=0 and y=z in projective coordinates. Canonical limbs; public inputs. -/
private def identityDifference (offset : Nat) : SAsm.Stmt := block <|
  ptr .x10 .x19 offset ++ [.ADDI .x28 .x0 0] ++
  ((List.range 5).flatMap fun i => [.LD .x5 .x10 (imm (8*i)), .OR .x28 .x28 .x5,
    .LD .x5 .x10 (imm (40+8*i)), .LD .x6 .x10 (imm (80+8*i)),
    .XOR .x5 .x5 .x6, .OR .x28 .x28 .x5])

private def subgroup (point : Nat) : Part := .seq [
  .asm (identityDifference point), failIf (.eq .x28 .x0) 11,
  multiply 3680 point 3600, .asm (identityDifference 3680), failIf (.ne .x28 .x0) 11]

private def hashChallenge : Part := .seq [
  .asm (block (ptr .x10 .x19 4096 ++ [.ADDI .x11 .x0 32])), .asm (copy .x10 .x20 .x11),
  .asm (block (ptr .x10 .x19 4128 ++ [.ADDI .x11 .x0 32])), .asm (copy .x10 .x8 .x11),
  hashMessage 64, reduce 1728 1856 64]

private def equation : Part := .seq [multiply 3680 1920 1824, multiply 2080 2080 1728,
  .asm (block (ptr .x10 .x19 2240 ++ ptr .x11 .x19 2240 ++ ptr .x12 .x19 2080 ++
    ptr .x13 .x19 2400)), .call 7,
  Point.operation 2 .x19 2400 .x19 3680 .x19 2320,
  Point.operation 2 .x19 2440 .x19 2240 .x19 3760,
  .asm (Decode.difference .x19 2400 2440), .asm (block [.ADDI .x22 .x28 0]),
  Point.operation 2 .x19 2400 .x19 3720 .x19 2320,
  Point.operation 2 .x19 2440 .x19 2280 .x19 3760,
  .asm (Decode.difference .x19 2400 2440),
  .asm (block [.OR .x28 .x28 .x22]), failIf (.ne .x28 .x0) 12]

/-- a0=key,a1=32,a2=message,a3=messageLen,a4=signature,a5=64,a6=work,a7=capacity.
No output; a0=status. Strict nonidentity prime-subgroup A/R, canonical A/R/S,
uncofactored equation. Status 10=encoding/point,11=subgroup,12=bad signature.
Workspace=messageLen+4160; stack=384. All verification inputs are public. -/
def verify : Except String SAsm.Stmt := program (.seq [setup true false,
  scalarCanonical, decode 2080 .x8, decode 2240 .x20,
  .asm (bytesConst .x19 3600 Scalar.order 32), subgroup 2080, subgroup 2240,
  hashChallenge, equation, finishOwned 0]) callees

end Libp2pAsm.Asm.Crypto.Curve25519.Verify
