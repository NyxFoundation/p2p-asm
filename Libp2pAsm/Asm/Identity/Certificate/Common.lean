import Libp2pAsm.Asm.Identity.X509.Certificate
import Libp2pAsm.Asm.Identity.PublicKey
import Libp2pAsm.Asm.Crypto.Curve25519.Verify
import Libp2pAsm.Asm.Crypto.Curve25519.Ed25519
import Libp2pAsm.Asm.Crypto.Weierstrass.Ecdsa
import Libp2pAsm.Asm.Crypto.RSA.Api
import Libp2pAsm.Spec.Identity.Certificate.Types
import Libp2pAsm.Spec.Crypto.SHA256

namespace Libp2pAsm.Asm.Identity.Certificate
open Rv64 Crypto.Util Crypto.Link
open Crypto.Curve25519 (ptr)

def stackBytes : Nat := 1552
def descriptorBytes : Nat := 192
def outputBytes : Nat := 192
def workBytes (n : Nat) : Nat := 8192 + 16*n
def workExpr : Crypto.Quic.Expr := fun r =>
  [.LD r .x10 8, .SLLI r r 4] ++ load .x7 8192 ++ [.ADD r r .x7]

/-- Root context: s0=descriptor,s1=work,s2=scratch,s3=scratch capacity,
s4=raw certificate,s5=length. s6..s11 are available to stages.
Work: parser0..168, subdescriptor176..304, output320..512,digest512..544,
signature arguments544..600,host view600..624,SHA256 table640..1152,
remaining budget1152,staging2048..(2215+n),then aligned scratch. -/
def cleanup : SAsm.Stmt := sequence [
  block [.ADDI .x11 .x2 (-1440), .ADDI .x12 .x0 1440], wipe .x11 .x12,
  block ([.SLLI .x12 .x21 4] ++ load .x7 8192 ++ [.ADD .x12 .x12 .x7]),
  wipe .x9 .x12, leave]

def fail (code : Nat) : SAsm.Stmt := sequence [
  block [.ADDI .x10 .x0 (imm code)], cleanup]

def require (condition : SAsm.Cond) (code : Nat) : SAsm.Stmt :=
  .ite condition empty (fail code)

def checked (callee code : Nat) : Part := .seq [
  .call callee, .asm (require (.eq .x10 .x0) code)]

/-- Public, conservative instruction reservation; not a universal cost proof.
Debit uses checked arithmetic and never increases caller budget. -/
def debit (amount : Reg) : SAsm.Stmt := sequence [
  block [.LD .x6 .x9 1152], require (.geu .x6 amount) 29,
  block [.SUB .x6 .x6 amount, .SD .x9 .x6 1152]]

def debitFixed (n : Nat) : SAsm.Stmt := sequence [block (load .x13 n), debit .x13]

def debitLinear (length : Reg) (factor fixed : Nat) : SAsm.Stmt := sequence [
  block (load .x7 factor ++ [.MULHU .x5 length .x7]), require (.eq .x5 .x0) 29,
  block [.MUL .x13 length .x7], debit .x13, debitFixed fixed]

def constants : SAsm.Stmt := block <|
  Spec.Crypto.SHA256.roundConstants.toList.zipIdx.flatMap fun (w,i) =>
    load .x5 w.toNat ++ [.SD .x9 .x5 (imm (640+8*i))]

def setup : SAsm.Stmt := sequence [enter,
  block [.ADDI .x8 .x10 0, .LD .x9 .x8 72, .LD .x20 .x8 0, .LD .x21 .x8 8,
    .ADDI .x22 .x21 167, .ANDI .x22 .x22 (-8)],
  block (load .x7 2048 ++ [.ADD .x22 .x22 .x7, .ADD .x18 .x9 .x22,
    .SLLI .x19 .x21 4] ++ load .x7 8192 ++
    [.ADD .x19 .x19 .x7, .ADDI .x12 .x19 0, .SUB .x19 .x19 .x22]),
  wipe .x9 .x12,
  block [.ADDI .x11 .x2 (-1440), .ADDI .x12 .x0 1440], wipe .x11 .x12,
  block [.LD .x5 .x8 96, .SD .x9 .x5 1152], constants]

def roleCheck : SAsm.Stmt := sequence [
  block [.LD .x5 .x10 24, .ADDI .x5 .x5 (-1), .ADDI .x7 .x0 2],
  reject (.geu .x5 .x7) 26]

def baseCheck : SAsm.Stmt := sequence [Crypto.Quic.descriptor descriptorBytes,
  block [.LD .x11 .x10 8, .SRLI .x5 .x11 56], reject (.ne .x5 .x0) 1,
  block [.LD .x5 .x10 16, .ADDI .x7 .x0 1], reject (.ne .x5 .x7) 1,
  roleCheck,
  block [.LD .x5 .x10 88], reject (.eq .x5 .x0) 29, reject (.ltu .x5 .x11) 29,
  block [.LD .x5 .x10 96], reject (.eq .x5 .x0) 29,
  block (workExpr .x12 ++ [.LD .x13 .x10 80]), reject (.ltu .x13 .x12) 5,
  block [.LD .x5 .x10 136, .ADDI .x7 .x0 (imm stackBytes)],
  reject (.ltu .x5 .x7) 5, Crypto.Quic.alignedField 72]

def parser : Part := .seq [
  .asm (sequence [debitLinear .x21 4096 1000000,
    block [.MULHU .x5 .x21 .x21], require (.eq .x5 .x0) 29,
    block [.MUL .x14 .x21 .x21], debitLinear .x14 128 0,
    block [.SD .x9 .x20 176, .SD .x9 .x21 184, .SD .x9 .x9 192,
      .ADDI .x5 .x0 168, .SD .x9 .x5 200, .SD .x9 .x18 208, .SD .x9 .x19 216,
      .LD .x5 .x8 88, .SD .x9 .x5 224, .LD .x5 .x8 96, .SD .x9 .x5 232,
      .ADDI .x10 .x9 176]]), checked 0 20]

/-- Pointer/length from a parser span. The parser proved the offsets fit raw. -/
def spanArgs (slot target : Nat) : SAsm.Stmt := block [
  .LD .x5 .x9 (imm slot), .ADD .x5 .x20 .x5, .SD .x9 .x5 (imm target),
  .LD .x5 .x9 (imm (slot+8)), .SD .x9 .x5 (imm (target+8))]

end Libp2pAsm.Asm.Identity.Certificate
