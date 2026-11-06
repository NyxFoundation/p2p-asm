import Libp2pAsm.Asm.Crypto.Curve25519.Point

namespace Libp2pAsm.Asm.Crypto.Curve25519.Decode
open Rv64 Util Link

private def f (id dst a b : Nat) : Part := fieldCall id .x19 dst a b
private def fail : Part := .seq [.asm (block [.ADDI .x10 .x0 10]), .asm leave]

/-- Compare canonical five-limb elements; OR difference in t3. -/
def difference (base : Reg) (a b : Nat) : SAsm.Stmt := block <|
  ptr .x10 base a ++ ptr .x11 base b ++ [.ADDI .x28 .x0 0] ++
  ((List.range 5).flatMap fun i => [.LD .x5 .x10 (imm (8*i)),
    .LD .x6 .x11 (imm (8*i)), .XOR .x5 .x5 .x6, .OR .x28 .x28 .x5])

private def pow (out input exponent : Nat) : Part := .seq [
  .asm (bytesConst .x19 280 exponent 32),
  .asm (block [.ADDI .x10 .x19 (imm out), .ADDI .x11 .x19 (imm input),
    .ADDI .x12 .x19 280, .ADDI .x13 .x19 312]), .call 6]

private def canonical : Part := .seq [
  .asm (block [.ADDI .x10 .x19 0, .ADDI .x11 .x9 0]), .call 3,
  .asm (block [.ADDI .x10 .x19 480, .ADDI .x11 .x19 0]), .call 4,
  .asm (block <| [.ADDI .x28 .x0 0] ++ ((List.range 32).flatMap fun i =>
    [.LBU .x5 .x9 (imm i), .LBU .x6 .x19 (imm (480+i))] ++
    (if i == 31 then [.SRLI .x18 .x5 7, .ANDI .x5 .x5 127] else []) ++
    [.XOR .x5 .x5 .x6, .OR .x28 .x28 .x5])),
  .ite (.ne .x28 .x0) fail (.asm empty)]

private def squareRoot : Part := .seq [
  .asm (fieldConst .x19 392 Point.d), .asm (fieldConst .x19 432 1),
  f 2 40 0 0, f 1 200 40 432, f 2 240 40 392, f 0 240 240 432,
  pow 160 240 (2^255-21), f 2 80 200 160,
  pow 120 80 ((2^255-16)/8), f 2 160 120 120,
  .asm (difference .x19 160 80),
  .ite (.ne .x28 .x0) (.seq [
    .asm (fieldConst .x19 432
      19681161376707505956807079304988542015446066515923890162744021073123829784752),
    f 2 120 120 432]) (.asm empty),
  f 2 160 120 120, .asm (difference .x19 160 80),
  .ite (.ne .x28 .x0) fail (.asm empty)]

private def sign : Part := .seq [
  .asm (fieldConst .x19 432 0), .asm (difference .x19 120 432),
  .ite (.eq .x28 .x0) (.ite (.ne .x18 .x0) fail (.asm empty)) (.asm empty),
  .asm (block [.LD .x5 .x19 120, .ANDI .x5 .x5 1]),
  .ite (.ne .x5 .x18) (f 1 120 432 120) (.asm empty)]

/-- a0=point160,a1=encoded32,a2=scratch512. For PUBLIC verification inputs only.
Rejects y>=p, nonresidues and negative zero; no destination writes on failure.
Status 10=invalid/noncanonical point. Top-level owner wipes scratch on all exits. -/
def body : Part := .seq [.asm enter,
  .asm (block [.ADDI .x8 .x10 0, .ADDI .x9 .x11 0, .ADDI .x19 .x12 0]),
  canonical, squareRoot, sign,
  .asm (block [.ADDI .x10 .x8 0, .ADDI .x11 .x19 120, .ADDI .x12 .x0 40]),
  .asm (copy .x10 .x11 .x12),
  .asm (block [.ADDI .x10 .x8 40, .ADDI .x11 .x19 0, .ADDI .x12 .x0 40]),
  .asm (copy .x10 .x11 .x12), .asm (fieldConst .x8 80 1),
  Point.operation 2 .x8 120 .x19 0 .x19 120,
  .asm (block [.ADDI .x10 .x0 0]), .asm leave]

end Libp2pAsm.Asm.Crypto.Curve25519.Decode
