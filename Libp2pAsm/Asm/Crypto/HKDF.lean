import Libp2pAsm.Asm.Crypto.HMAC

namespace Libp2pAsm.Asm.Crypto.HKDF
open Rv64 Util Link

/-- Same ABI as HMAC: key=salt, message=IKM. A zero salt length encodes either
none or some []; both equal the RFC default 32 zero bytes, without reading salt. -/
def extract : Except String SAsm.Stmt := HMAC.sha256

/-- x28=max HMAC message length, x30=aligned HMAC offset, x29=total capacity.
The caller has checked info before this nonwrapping arithmetic. -/
def sizes : SAsm.Stmt := sequence [
  block [.ADDI .x28 .x13 1, .ADDI .x7 .x0 32],
  .ite (.ltu .x7 .x15) (block [.ADDI .x28 .x28 32]) empty,
  block [.ADDI .x30 .x28 39, .ANDI .x30 .x30 (-8),
    .ADDI .x29 .x28 864, .ADDI .x7 .x0 896],
  .ite (.ltu .x29 .x7) (block [.ADDI .x29 .x7 0]) empty,
  block [.ADD .x29 .x29 .x30]]

private def lengths : SAsm.Stmt := sequence [
  block (load .x7 8160), reject (.ltu .x7 .x15) 2,
  block [.ADDI .x7 .x0 32], reject (.ltu .x11 .x7) 3,
  .ite (.eq .x15 .x0) (finish 0) empty,
  block [.SRLI .x5 .x11 61], reject (.ne .x5 .x0) 1,
  block (load .x7 (2^61-65) ++ [.ADDI .x5 .x0 32]),
  .ite (.ltu .x5 .x15) (block [.ADDI .x7 .x7 (-32)]) empty,
  reject (.geu .x13 .x7) 1]

/-- Constants are the ninth standard ABI argument at 0(sp), a readable LE64 slot. -/
def validate : SAsm.Stmt := sequence [lengths, sizes,
  reject (.ltu .x17 .x29) 5,
  range .x10 .x11, range .x12 .x13, range .x14 .x15, range .x16 .x29,
  block [.LD .x31 .x2 0, .ADDI .x7 .x0 512], range .x31 .x7,
  block [.OR .x5 .x16 .x31, .ANDI .x5 .x5 7], reject (.ne .x5 .x0) 4]

private def setup : SAsm.Stmt := sequence [enter,
  block [.ADDI .x8 .x10 0, .ADDI .x9 .x11 0, .ADDI .x18 .x12 0,
    .ADDI .x19 .x13 0, .ADDI .x20 .x14 0, .ADDI .x21 .x15 0,
    .ADDI .x22 .x16 0, .LD .x23 .x2 112, .ADDI .x24 .x29 0,
    .ADDI .x25 .x30 0, .ADDI .x26 .x0 1, .ADDI .x27 .x0 0]]

private def message : SAsm.Stmt := sequence [
  block [.ADDI .x10 .x22 32], copy .x10 .x22 .x27,
  block [.ADDI .x10 .x22 32, .ADD .x10 .x10 .x27], copy .x10 .x18 .x19,
  block [.ADD .x5 .x10 .x19, .SB .x5 .x26 0]]

private def hmacArgs : SAsm.Stmt := block [
  .ADDI .x10 .x8 0, .ADDI .x11 .x9 0, .ADDI .x12 .x22 32,
  .ADD .x13 .x19 .x27, .ADDI .x13 .x13 1, .ADDI .x14 .x22 0,
  .ADD .x15 .x22 .x25, .SUB .x16 .x24 .x25, .ADDI .x17 .x23 0]

private def output : SAsm.Stmt := sequence [
  block [.ADDI .x28 .x0 32],
  .ite (.ltu .x21 .x28) (block [.ADDI .x28 .x21 0]) empty,
  -- copy uses t3; keep the chosen length in a caller-saved register instead.
  block [.ADDI .x11 .x28 0], copy .x20 .x22 .x11,
  block [.ADD .x20 .x20 .x11, .SUB .x21 .x21 .x11,
    .ADDI .x26 .x26 1, .ADDI .x27 .x0 32]]

/-- a0=PRK,a1=PRKlen,a2=info,a3=infoLen,a4=out,a5=L,a6=workspace,a7=capacity;
0(sp)=constants. Required capacity is align8(32+m)+max(896,864+m),
m=infoLen+1+(if L>32 then 32 else 0). L=0 needs no workspace/input reads.
Workspace [0,32)=T, [32,32+m)=HMAC message, aligned suffix=HMAC workspace.
Stack depth 400, plus the caller's unmodified ninth-argument slot at/above sp. -/
def expand : Except String SAsm.Stmt := program (.seq [
  .asm validate, .asm setup,
  .loop (.ne .x21 .x0) (.seq [.asm message, .asm hmacArgs, .call 1, .asm output]),
  .asm (wipe .x22 .x24), .asm (block [.ADDI .x10 .x0 0]), .asm leave])
  [.asm (Whole.body .sha256), HMAC.body]

end Libp2pAsm.Asm.Crypto.HKDF
