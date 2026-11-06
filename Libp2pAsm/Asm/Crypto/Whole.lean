import Libp2pAsm.Asm.Crypto.Util

namespace Libp2pAsm.Asm.Crypto.Whole
open Rv64 Util Sha2

def blockBytes (v : Variant) : Nat := 2*v.width
def digestBytes (v : Variant) : Nat := v.width
def workspaceBytes (v : Variant) : Nat := 64 + 8*v.rounds + 2*blockBytes v

def iv (v : Variant) : List Nat := match v with
  | .sha256 => [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
      0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  | .sha512 => [0x6a09e667f3bcc908, 0xbb67ae8584caa73b,
      0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1, 0x510e527fade682d1,
      0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

def validate (v : Variant) : SAsm.Stmt := sequence [
  if v == .sha256 then sequence [block [.SRLI .x5 .x11 61],
    reject (.ne .x5 .x0) 1] else empty,
  capacity .x14 (workspaceBytes v), range .x10 .x11,
  block [.ADDI .x7 .x0 (imm (digestBytes v))], range .x12 .x7,
  block [.ADDI .x7 .x0 (imm (workspaceBytes v))], range .x13 .x7,
  block [.ADDI .x7 .x0 (imm (8*v.rounds))], range .x15 .x7,
  block [.OR .x5 .x13 .x15, .ANDI .x5 .x5 7], reject (.ne .x5 .x0) 4]

private def setup (v : Variant) : SAsm.Stmt := sequence [enter,
  block [.ADDI .x8 .x10 0, .ADDI .x9 .x11 0, .ADDI .x18 .x12 0,
    .ADDI .x19 .x13 0, .ADDI .x20 .x15 0, .ADDI .x21 .x11 0,
    .ADDI .x22 .x0 (imm (blockBytes v)),
    .ADDI .x23 .x19 (imm (64+8*v.rounds)),
    .ADDI .x24 .x0 (imm (workspaceBytes v))],
  wipe .x19 .x24,
  block (iv v |>.zipIdx.flatMap fun (n, i) =>
    load .x5 n ++ [.SD .x19 .x5 (imm (8*i))])]

/-- s0 points at a block; s3 workspace; s4 immutable table. Restores every s-reg. -/
def compressAt (v : Variant) : SAsm.Stmt := sequence [
  block [.ADDI .x10 .x19 0, .ADDI .x11 .x8 0,
    .ADDI .x12 .x19 64, .ADDI .x13 .x20 0], compressBody v]

private def fullBlocks (v : Variant) : SAsm.Stmt :=
  .loop (.geu .x9 .x22) (sequence [compressAt v,
    block [.ADD .x8 .x8 .x22, .SUB .x9 .x9 .x22]])

/-- The 128-bit SHA-512 bit length is (byteLength >> 61, byteLength << 3). -/
def lengthField (v : Variant) (tail total : Reg) : SAsm.Stmt := block <|
  (if v == .sha512 then
    [.SRLI .x6 total 61] ++ storeBE tail .x6 (blockBytes v - 16) 8 else []) ++
  [.SLLI .x6 total 3] ++ storeBE tail .x6 (blockBytes v - 8) 8

private def paddedBlocks (v : Variant) : SAsm.Stmt := sequence [
  copy .x23 .x8 .x9,
  block [.ADD .x5 .x23 .x9, .ADDI .x6 .x0 128, .SB .x5 .x6 0,
    .ADDI .x25 .x23 0, .ADDI .x26 .x0 1,
    .ADDI .x7 .x0 (imm (blockBytes v - v.width/4))],
  .ite (.geu .x9 .x7) (block [.ADD .x25 .x25 .x22, .ADDI .x26 .x0 2]) empty,
  lengthField v .x25 .x21,
  block [.ADDI .x8 .x23 0],
  .loop (.ne .x26 .x0) (sequence [compressAt v,
    block [.ADD .x8 .x8 .x22, .ADDI .x26 .x26 (-1)]])]

private def output (v : Variant) : SAsm.Stmt := block <|
  (List.range 8).flatMap fun i =>
    [.LD .x6 .x19 (imm (8*i))] ++ storeBE .x18 .x6 (i*(v.width/8)) (v.width/8)

/-- No-validation internal leaf, only for callers that establish validate's checks.
ABI a0=input, a1=bytes, a2=output, a3=workspace, a4=capacity, a5=constants.
Workspace=704/960 bytes, 8-aligned; stack=176 bytes including compression.
Input/output may be unaligned; input is untouched when length is zero.
Result a0=0; caller-saved temporaries and all used workspace/stack bytes are wiped.
All ranges are caller-owned, valid, disjoint, and disjoint from code/stack/table. -/
def body (v : Variant) : SAsm.Stmt := sequence [setup v,
  fullBlocks v, paddedBlocks v, output v, wipe .x19 .x24,
  block [.ADDI .x10 .x0 0], leave]

/-- Checked standard leaf. Errors 1=SHA bit length, 4=address/alignment, 5=capacity.
All rejection paths precede memory access and preserve output/workspace/stack. -/
def hash (v : Variant) : SAsm.Stmt := sequence [validate v, body v]

end Libp2pAsm.Asm.Crypto.Whole
