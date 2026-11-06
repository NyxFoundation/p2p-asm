import Libp2pAsm.Asm.Crypto.Curve25519.Decode
import Libp2pAsm.Asm.Crypto.Curve25519.Scalar
import Libp2pAsm.Asm.Crypto.Whole
import Libp2pAsm.Spec.Crypto.SHA512

namespace Libp2pAsm.Asm.Crypto.Curve25519.Edwards
open Rv64 Util Link

def overhead : Nat := 4160
def stackBytes : Nat := 384

def callees : List Part := Point.callees ++ [Decode.body, Scalar.reduce, Scalar.mulAdd,
  .asm (Whole.body .sha512)]

/-- All lengths and all accessed owned ranges checked before any memory access.
Workspace = messageLen+4160; SHA-512 supports the entire resulting ABI range. -/
def validate (verify keygen : Bool) : SAsm.Stmt := sequence [
  block [.ADDI .x7 .x0 32], reject (.ne .x11 .x7) 8,
  if verify then sequence [block [.ADDI .x7 .x0 64], reject (.ne .x15 .x7) 8]
    else capacity .x15 (if keygen then 32 else 64),
  block (load .x7 (2^64-overhead)), reject (.geu .x13 .x7) 1,
  block (load .x29 overhead ++ [.ADD .x29 .x29 .x13]), reject (.ltu .x17 .x29) 5,
  block [.ADDI .x30 .x0 32], range .x10 .x30,
  range .x12 .x13, block [.ADDI .x28 .x0 (if keygen then 32 else 64)], range .x14 .x28,
  range .x16 .x29, block [.ANDI .x5 .x16 7], reject (.ne .x5 .x0) 4,
  stackCheck stackBytes,
  disjoint .x16 .x29 .x10 .x30, disjoint .x16 .x29 .x12 .x13,
  disjoint .x16 .x29 .x14 .x28,
  if verify then empty else sequence [disjoint .x14 .x28 .x10 .x30,
    disjoint .x14 .x28 .x12 .x13],
  block [.ADDI .x31 .x2 (-384), .ADDI .x7 .x0 384],
  disjoint .x31 .x7 .x10 .x30, disjoint .x31 .x7 .x12 .x13,
  disjoint .x31 .x7 .x14 .x28, disjoint .x31 .x7 .x16 .x29]

private def table : SAsm.Stmt := block <|
  Spec.Crypto.SHA512.roundConstants.toList.zipIdx.flatMap fun (v,i) =>
    load .x5 v.toNat ++ [.SD .x19 .x5 (imm (8*i))]

def setup (verify keygen : Bool) : Part := .seq [.asm (validate verify keygen), .asm enter,
  .asm (block [.ADDI .x8 .x10 0, .ADDI .x9 .x12 0, .ADDI .x18 .x13 0,
    .ADDI .x19 .x16 0, .ADDI .x20 .x14 0, .ADDI .x21 .x29 0,
    .ADDI .x30 .x2 (-272), .ADDI .x11 .x0 272]),
  .asm (wipe .x30 .x11), .asm table, .asm (Point.basePoint .x19 1920)]

def finishOwned (status : Nat) : Part := .seq [.asm (wipe .x19 .x21),
  .asm (block [.ADDI .x10 .x0 (imm status)]), .asm leave]

/-- Input pointer in a0 and byte count in a1; output offset is public. -/
def hash (out : Nat) : Part := .seq [
  .asm (block (ptr .x12 .x19 out ++ ptr .x13 .x19 640 ++
    [.ADDI .x14 .x0 960, .ADDI .x15 .x19 0])), .call 13]

def reduce (out input count : Nat) : Part := .seq [
  .asm (block (ptr .x10 .x19 out ++ ptr .x11 .x19 input ++ [.ADDI .x12 .x0 (imm count)])),
  .call 11]

def multiply (out point scalar : Nat) : Part := .seq [
  .asm (block (ptr .x10 .x19 out ++ ptr .x11 .x19 point ++ ptr .x12 .x19 scalar ++
    ptr .x13 .x19 2400)), .call 8]

def encode (out point : Nat) : Part := .seq [
  .asm (block (ptr .x10 .x19 out ++ ptr .x11 .x19 point ++ ptr .x12 .x19 2400)), .call 9]

def copyAt (dst src count : Nat) : Part := .seq [
  .asm (block (ptr .x10 .x19 dst ++ ptr .x11 .x19 src ++ [.ADDI .x12 .x0 (imm count)])),
  .asm (copy .x10 .x11 .x12)]

/-- SHA-512 seed expansion, RFC pruning, and actual scalar multiplication. -/
def expandKey : Part := .seq [
  .asm (block [.ADDI .x10 .x8 0, .ADDI .x11 .x0 32]), hash 1600,
  .asm (block [.LBU .x5 .x19 1600, .ANDI .x5 .x5 248, .SB .x19 .x5 1600,
    .LBU .x5 .x19 1631, .ANDI .x5 .x5 63, .ORI .x5 .x5 64, .SB .x19 .x5 1631]),
  multiply 2080 1920 1600, encode 1760 2080]

def hashMessage (prefixBytes : Nat) : Part := .seq [
  .asm (block (ptr .x10 .x19 (4096+prefixBytes))), .asm (copy .x10 .x9 .x18),
  .asm (block (ptr .x10 .x19 4096 ++ [.ADDI .x11 .x18 (imm prefixBytes)])), hash 1856]

def publish (src count : Nat) : Part := .seq [
  .asm (block (ptr .x11 .x19 src ++ [.ADDI .x12 .x0 (imm count)])),
  .asm (copy .x20 .x11 .x12), finishOwned 0]

end Libp2pAsm.Asm.Crypto.Curve25519.Edwards
