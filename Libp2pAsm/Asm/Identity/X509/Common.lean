import Libp2pAsm.Asm.Crypto.Quic.Common
import Libp2pAsm.Asm.Codec.Der
import Libp2pAsm.Asm.Identity.Time
import Libp2pAsm.Asm.Identity.X509.Algorithm

namespace Libp2pAsm.Asm.Identity.X509
open Rv64 Crypto.Util Crypto.Link

/-! Internal parser convention: s0 failure continuation,s1 input,s2 input length,s3 output,
s4 work,s5 cursor offset,s6 limit,s7 node offset,s8 node total,s9 content offset,
s10 content length,s11 operation budget. These are restored only by the root.
Work[0,168) is staged output;[168,480) context;480=root frame;[512,512+4*n)
holds seen OID views. Owned stack is144:112 root+at most two16-byte helpers. -/
def workSize : Crypto.Quic.Expr := fun r =>
  [.LD r .x10 8, .SLLI r r 2, .ADDI r r 512]

def preflight : SAsm.Stmt := sequence [
  Crypto.Quic.descriptor 64,
  block [.LD .x11 .x10 8, .SRLI .x5 .x11 61], reject (.ne .x5 .x0) 2,
  block [.LD .x12 .x10 48], reject (.eq .x12 .x0) 12, reject (.ltu .x12 .x11) 12,
  block [.LD .x12 .x10 56], reject (.eq .x12 .x0) 12,
  block [.LD .x12 .x10 24, .ADDI .x7 .x0 168], reject (.ltu .x12 .x7) 5,
  block (workSize .x12 ++ [.LD .x13 .x10 40]), reject (.ltu .x13 .x12) 5,
  Crypto.Quic.alignedField 32,
  Crypto.Quic.spans 64 144 [Crypto.Quic.variableSpan 0 8,
    Crypto.Quic.fixed 16 168, ⟨Crypto.Quic.field 32, workSize⟩]]

def setup : SAsm.Stmt := sequence [enter,
  block [.LD .x9 .x10 0, .LD .x18 .x10 8,
    .LD .x19 .x10 16, .LD .x20 .x10 32, .LD .x27 .x10 56,
    .SLLI .x21 .x18 2, .ADDI .x21 .x21 512],
  wipe .x20 .x21,
  block [.SD .x20 .x2 480, .ADDI .x5 .x0 1, .SD .x20 .x5 400,
    .ADDI .x5 .x0 3, .SD .x20 .x5 408, .ADDI .x21 .x0 0, .ADDI .x22 .x18 0]]

/-- May be entered from a private helper: restore root sp before wiping. -/
def cleanup : SAsm.Stmt := sequence [
  block [.LD .x2 .x20 480, .ADDI .x21 .x2 (-32), .ADDI .x22 .x0 32],
  wipe .x21 .x22,
  block [.SLLI .x21 .x18 2, .ADDI .x21 .x21 512], wipe .x20 .x21, leave]

/-- Internal callee7 returns the position-independent address of the cleanup
immediately after its RET. Failures jump there without growing the call stack.
This keeps conditional skips inside RV64 branch reach; only s0 holds the target. -/
def handlerAddress : SAsm.Stmt := sequence [
  block [.AUIPC .x8 0, .ADDI .x8 .x8 12], .ret, cleanup]

def fail (status : Nat) : SAsm.Stmt := sequence [
  block [.ADDI .x10 .x0 (imm status), .ADDI .x1 .x8 0], .ret]

def require (condition : SAsm.Cond) (status : Nat := 6) : SAsm.Stmt :=
  .ite condition empty (fail status)

def tick : SAsm.Stmt := sequence [
  require (.ne .x27 .x0) 12, block [.ADDI .x27 .x27 (-1)]]

def nextNode : Part := .seq [
  .asm (sequence [tick, require (.geu .x22 .x21),
    block [.ADDI .x23 .x21 0, .ADD .x10 .x9 .x21, .SUB .x11 .x22 .x21]]),
  .call 0,
  .asm (.ite (.ne .x10 .x0) (sequence [block [.ADDI .x5 .x0 1],
    .ite (.eq .x10 .x5) (fail 1) (fail 6)]) empty),
  .asm (block [.ADDI .x24 .x14 0, .ADD .x25 .x23 .x12,
    .ADDI .x26 .x13 0, .ADD .x21 .x23 .x14])]

def expectNode (tag : Nat) : Part := .seq [nextNode,
  .asm (sequence [block [.ADDI .x5 .x0 (imm tag)], require (.eq .x11 .x5)])]

def enterNode : SAsm.Stmt := block [.ADDI .x21 .x25 0, .ADD .x22 .x25 .x26]
def endNode : SAsm.Stmt := require (.eq .x21 .x22)
def saveCursor (slot : Nat) : SAsm.Stmt :=
  block [.SD .x20 .x21 (imm slot), .SD .x20 .x22 (imm (slot+8))]
def restoreCursor (slot : Nat) : SAsm.Stmt :=
  block [.LD .x21 .x20 (imm slot), .LD .x22 .x20 (imm (slot+8))]
def saveSpan (slot : Nat) (content : Bool := false) : SAsm.Stmt :=
  block [.SD .x20 (if content then .x25 else .x23) (imm slot),
    .SD .x20 (if content then .x26 else .x24) (imm (slot+8))]

def helperEnter : SAsm.Stmt := block [.ADDI .x2 .x2 (-16), .SD .x2 .x1 0]
def helperLeave : SAsm.Stmt := sequence [
  block [.LD .x1 .x2 0, .SD .x2 .x0 0, .SD .x2 .x0 8, .ADDI .x2 .x2 16], .ret]

def algorithm (callee slot : Nat) : Part := .seq [
  .asm (sequence [tick, block [.ADD .x10 .x9 .x23, .ADDI .x11 .x24 0]]),
  .call callee,
  .asm (sequence [require (.eq .x10 .x0) 8, block [.SD .x20 .x11 (imm slot)]])]

def calendar (slot : Nat) : Part := .seq [
  .asm (sequence [tick, block [.ADDI .x10 .x11 0, .ADD .x11 .x9 .x25, .ADDI .x12 .x26 0]]),
  .call 3,
  .asm (sequence [require (.eq .x10 .x0), block [.SD .x20 .x11 (imm slot)]])]

def unsignedInteger : SAsm.Stmt := sequence [
  require (.ne .x26 .x0),
  block [.ADD .x5 .x9 .x25, .LBU .x6 .x5 0, .ADDI .x7 .x0 128],
  require (.ltu .x6 .x7),
  .ite (.eq .x6 .x0) (sequence [block [.ADDI .x7 .x0 1],
    .ite (.ltu .x7 .x26) (sequence [
      block [.LBU .x6 .x5 1, .ADDI .x7 .x0 128], require (.geu .x6 .x7),
      block [.ADDI .x25 .x25 1, .ADDI .x26 .x26 (-1)]]) empty]) empty]

def bitString : SAsm.Stmt := sequence [require (.ne .x26 .x0),
  block [.ADD .x5 .x9 .x25, .LBU .x6 .x5 0], require (.eq .x6 .x0),
  block [.ADDI .x25 .x25 1, .ADDI .x26 .x26 (-1)]]

/-- Boolean result in a1, no normalization of non-00/FF encodings. -/
def boolean : SAsm.Stmt := sequence [
  block [.ADDI .x5 .x0 1], require (.eq .x26 .x5),
  block [.ADD .x5 .x9 .x25, .LBU .x11 .x5 0],
  .ite (.ne .x11 .x0) (sequence [block [.ADDI .x5 .x0 255],
    require (.eq .x11 .x5), block [.ADDI .x11 .x0 1]]) empty]

def validOid : SAsm.Stmt := sequence [require (.ne .x26 .x0),
  block [.ADD .x10 .x9 .x25, .ADDI .x11 .x26 0, .ADDI .x12 .x0 1],
  .loop (.ne .x11 .x0) (sequence [tick,
    block [.LBU .x13 .x10 0, .ADDI .x5 .x0 128, .SLTU .x14 .x13 .x5],
    .ite (.eq .x14 .x0) (.ite (.ne .x12 .x0) (require (.ne .x13 .x5)) empty) empty,
    block [.ADDI .x12 .x14 0, .ADDI .x10 .x10 1, .ADDI .x11 .x11 (-1)]]),
  require (.ne .x12 .x0)]

/-- Compare the current content view to a fixed public byte string; a1=equal. -/
def equalBytes (bytes : List Nat) : SAsm.Stmt := sequence [
  block [.ADDI .x11 .x0 0, .ADDI .x5 .x0 (imm bytes.length)],
  .ite (.eq .x26 .x5) (sequence [
    block ([.ADD .x12 .x9 .x25, .ADDI .x13 .x0 0] ++
      bytes.zipIdx.flatMap (fun (b,i) => [.LBU .x14 .x12 (imm i),
        .XORI .x14 .x14 (imm b), .OR .x13 .x13 .x14]) ++
      [.SLTU .x11 .x0 .x13, .XORI .x11 .x11 1])]) empty]

end Libp2pAsm.Asm.Identity.X509
