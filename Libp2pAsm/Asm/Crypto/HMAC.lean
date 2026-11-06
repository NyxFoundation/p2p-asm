import Libp2pAsm.Asm.Crypto.Link
import Libp2pAsm.Asm.Crypto.Whole

namespace Libp2pAsm.Asm.Crypto.HMAC
open Rv64 Util Link

/-- Required bytes=max(896,864+messageLength). Called only after length checks. -/
def required : SAsm.Stmt := sequence [
  block [.ADDI .x29 .x13 864, .ADDI .x7 .x0 896],
  .ite (.ltu .x29 .x7) (block [.ADDI .x29 .x7 0]) empty]

def validate : SAsm.Stmt := sequence [
  block [.SRLI .x5 .x11 61], reject (.ne .x5 .x0) 1,
  block (load .x7 (2^61-64)), reject (.geu .x13 .x7) 1,
  required, reject (.ltu .x16 .x29) 5,
  range .x10 .x11, range .x12 .x13, range .x15 .x29,
  block [.ADDI .x7 .x0 32], range .x14 .x7,
  block [.ADDI .x7 .x0 512], range .x17 .x7,
  block [.OR .x5 .x15 .x17, .ANDI .x5 .x5 7], reject (.ne .x5 .x0) 4]

private def setup : SAsm.Stmt := sequence [required, enter,
  block [.ADDI .x8 .x10 0, .ADDI .x9 .x11 0, .ADDI .x18 .x12 0,
    .ADDI .x19 .x13 0, .ADDI .x20 .x14 0, .ADDI .x21 .x15 0,
    .ADDI .x22 .x17 0, .ADDI .x23 .x29 0, .ADDI .x24 .x15 800,
    .ADDI .x25 .x0 64], wipe .x21 .x25]

/-- Prepare the private SHA leaf; table and workspace have already been checked. -/
private def hashArgs (input length output : Reg) : SAsm.Stmt := block [
  .ADDI .x10 input 0, .ADDI .x11 length 0, .ADDI .x12 output 0,
  .ADDI .x13 .x21 96, .ADDI .x14 .x0 704, .ADDI .x15 .x22 0]

private def normalize : Part := .ite (.ltu .x25 .x9)
  (.seq [.asm (hashArgs .x8 .x9 .x21), .call 0])
  (.asm (copy .x21 .x8 .x9))

private def pad (value : Nat) : SAsm.Stmt := sequence [
  block [.ADDI .x5 .x21 0, .ADDI .x6 .x24 0, .ADDI .x7 .x0 64],
  .loop (.ne .x7 .x0) (block [.LBU .x28 .x5 0, .XORI .x28 .x28 (imm value),
    .SB .x6 .x28 0, .ADDI .x5 .x5 1, .ADDI .x6 .x6 1, .ADDI .x7 .x7 (-1)])]

private def inner : Part := .seq [
  .asm (pad 0x36), .asm (block [.ADDI .x26 .x24 64]),
  .asm (copy .x26 .x18 .x19),
  .asm (block [.ADDI .x26 .x19 64, .ADDI .x27 .x21 64]),
  .asm (hashArgs .x24 .x26 .x27), .call 0]

private def outer : Part := .seq [
  .asm (pad 0x5c), .asm (block [.ADDI .x26 .x24 64,
    .ADDI .x27 .x21 64, .ADDI .x25 .x0 32]),
  .asm (copy .x26 .x27 .x25),
  .asm (block [.ADDI .x26 .x0 96]),
  .asm (hashArgs .x24 .x26 .x20), .call 0]

/-- Private prevalidated leaf, callee 0=Whole.body sha256.
Workspace: key[0,64), innerDigest[64,96), SHA[96,800), concat[800,required).
Stack depth 288 including nested SHA and compression; frame itself is 112 bytes.
No secret-dependent decisions: key length, message length, and counters are public. -/
def body : Part := .seq [.asm setup, normalize, inner, outer,
  .asm (wipe .x21 .x23), .asm (block [.ADDI .x10 .x0 0]), .asm leave]

/-- a0=key,a1=keyLen,a2=message,a3=messageLen,a4=out32,
a5=workspace,a6=capacity,a7=immutable SHA256 constants. All s-regs/ra/sp/gp/tp
are preserved; other caller-saved registers cleared; a0=status. Validation is
before all secret access. Workspace is 8-aligned, inputs/output may be unaligned. -/
def sha256 : Except String SAsm.Stmt :=
  program (.seq [.asm validate, body]) [.asm (Whole.body .sha256)]

end Libp2pAsm.Asm.Crypto.HMAC
