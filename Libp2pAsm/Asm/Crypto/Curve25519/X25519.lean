import Libp2pAsm.Asm.Crypto.Curve25519.Common

namespace Libp2pAsm.Asm.Crypto.Curve25519.X25519
open Rv64 Util Link

def workspaceBytes : Nat := 896
def stackBytes : Nat := 272

private def validate (basePoint : Bool) : SAsm.Stmt := sequence [
  block [.ADDI .x7 .x0 32], reject (.ne .x11 .x7) 8,
  if basePoint then empty else reject (.ne .x13 .x7) 8,
  capacity .x15 32, capacity .x17 workspaceBytes,
  block [.ADDI .x30 .x0 32, .ADDI .x29 .x0 (imm workspaceBytes)],
  range .x10 .x30, if basePoint then empty else range .x12 .x30,
  range .x14 .x30, range .x16 .x29,
  block [.ANDI .x5 .x16 7], reject (.ne .x5 .x0) 4, stackCheck stackBytes,
  block [.ADDI .x28 .x2 (BitVec.ofInt 12 (-Int.ofNat stackBytes)),
    .ADDI .x31 .x0 (imm stackBytes)],
  disjoint .x10 .x30 .x14 .x30, disjoint .x10 .x30 .x16 .x29,
  disjoint .x10 .x30 .x28 .x31, disjoint .x14 .x30 .x16 .x29,
  disjoint .x14 .x30 .x28 .x31, disjoint .x16 .x29 .x28 .x31,
  if basePoint then empty else sequence [disjoint .x12 .x30 .x14 .x30,
    disjoint .x12 .x30 .x16 .x29, disjoint .x12 .x30 .x28 .x31]]

private def finishOwned (status : Nat) : Part := .seq [
  .asm (block [.ADDI .x11 .x0 (imm workspaceBytes)]), .asm (wipe .x19 .x11),
  .asm (block [.ADDI .x10 .x0 (imm status)]), .asm leave]

private def f (op out a b : Nat) : Part := fieldCall op .x19 out a b

/-- x2,z2 -> 2P. The public peer undergoes three doubles before any secret read.
A zero projective denominator detects the complete low-order subgroup on either
curve/twist, independently of the supplied secret. -/
private def double : Part := .seq [f 0 264 104 144, f 2 304 264 264,
  f 1 344 104 144, f 2 384 344 344, f 1 424 304 384,
  f 2 104 304 384, f 2 624 424 824, f 0 624 624 304, f 2 144 424 624]

private def checkPeer : Part := .seq [
  .asm (block [.ADDI .x10 .x19 104, .ADDI .x11 .x19 64, .ADDI .x12 .x0 40]),
  .asm (copy .x10 .x11 .x12), .asm (fieldConst .x19 144 1),
  double, double, double,
  .asm (block <| [.ADDI .x28 .x0 0] ++ ((List.range 5).flatMap fun i =>
    [.LD .x5 .x19 (imm (144+8*i)), .OR .x28 .x28 .x5])),
  .ite (.eq .x28 .x0) (finishOwned 9) (.asm empty)]

private def swapPoints (bit : Reg) : Part := .seq [
  .asm (block [.ADDI .x10 .x19 104, .ADDI .x11 .x19 184, .ADDI .x12 bit 0]), .call 5,
  .asm (block [.ADDI .x10 .x19 144, .ADDI .x11 .x19 224, .ADDI .x12 bit 0]), .call 5]

private def ladderStep : Part := .seq [
  .asm (block [.ADDI .x20 .x20 (-1), .SRLI .x5 .x20 3, .ADD .x5 .x19 .x5,
    .LBU .x22 .x5 0, .ANDI .x6 .x20 7, .SRL .x22 .x22 .x6,
    .ANDI .x22 .x22 1, .XOR .x21 .x21 .x22]), swapPoints .x21,
  .asm (block [.ADDI .x21 .x22 0]),
  f 0 264 104 144, f 2 304 264 264, f 1 344 104 144, f 2 384 344 344,
  f 1 424 304 384, f 0 464 184 224, f 1 504 184 224,
  f 2 544 504 264, f 2 584 464 344,
  f 0 624 544 584, f 2 184 624 624,
  f 1 624 544 584, f 2 224 624 624, f 2 224 224 64,
  f 2 104 304 384, f 2 624 424 824, f 0 624 304 624, f 2 144 424 624]

private def setup (basePoint shared : Bool) : Part := .seq [
  .asm (validate basePoint), .asm enter,
  .asm (block [.ADDI .x8 .x10 0, .ADDI .x9 .x12 0,
    .ADDI .x18 .x14 0, .ADDI .x19 .x16 0]),
  .asm (fieldConst .x19 824 121665),
  if basePoint then .asm (fieldConst .x19 64 9) else .seq [
    .asm (block [.ADDI .x10 .x19 64, .ADDI .x11 .x9 0]), .call 3],
  if shared then checkPeer else .asm empty,
  .asm (block [.ADDI .x11 .x0 32]), .asm (copy .x19 .x8 .x11),
  .asm (block [.LBU .x5 .x19 0, .ANDI .x5 .x5 248, .SB .x19 .x5 0,
    .LBU .x5 .x19 31, .ANDI .x5 .x5 127, .ORI .x5 .x5 64, .SB .x19 .x5 31,
    .ADDI .x20 .x0 255, .ADDI .x21 .x0 0]),
  .asm (fieldConst .x19 104 1), .asm (fieldConst .x19 144 0),
  .asm (block [.ADDI .x10 .x19 184, .ADDI .x11 .x19 64, .ADDI .x12 .x0 40]),
  .asm (copy .x10 .x11 .x12), .asm (fieldConst .x19 224 1)]

private def body (basePoint shared : Bool) : Part := .seq [setup basePoint shared,
  .loop (.ne .x20 .x0) ladderStep, swapPoints .x21,
  .asm (bytesConst .x19 784 (2^255-21) 32),
  .asm (block [.ADDI .x10 .x19 664, .ADDI .x11 .x19 144,
    .ADDI .x12 .x19 784, .ADDI .x13 .x19 704]), .call 6,
  f 2 664 664 104,
  .asm (block [.ADDI .x10 .x18 0, .ADDI .x11 .x19 664]), .call 4, finishOwned 0]

/-- a0=secret,a1=32,a2=peer,a3=32,a4=output,a5=outCapacity,a6=work,a7=capacity.
Output=32 bytes; workspace=896, stack=272. Status 8=length,9=low-order peer,
4=range/alignment/overlap,5=capacity. Read-only inputs may overlap each other.
All owned writable ranges must be disjoint; mapping/code separation are contracts. -/
def sharedSecret : Except String SAsm.Stmt := program (body false true) arithmeticCallees

/-- RFC primitive, including zero results. Same ABI as sharedSecret. -/
def raw : Except String SAsm.Stmt := program (body false false) arithmeticCallees

/-- a0=secret,a1=32,a2=output,a3=outCapacity,a4=work,a5=capacity. -/
def publicKey : Except String SAsm.Stmt := program (.seq [
  .asm (block [.ADDI .x16 .x14 0, .ADDI .x17 .x15 0,
    .ADDI .x14 .x12 0, .ADDI .x15 .x13 0]), body true false]) arithmeticCallees

end Libp2pAsm.Asm.Crypto.Curve25519.X25519
