import Libp2pAsm.Asm.Codec.ProtobufVarint
import Libp2pAsm.Asm.Crypto.Curve25519.Common

namespace Libp2pAsm.Asm.Identity.PublicKey
open Rv64 Crypto.Util Crypto.Link
open Crypto.Curve25519 (disjoint stackCheck)

/-- Preserve the three decoded fields while restoring and wiping the root frame. -/
private def leaveValues : SAsm.Stmt := sequence [block <|
  (saved.zipIdx.flatMap fun (r, i) =>
    [.LD r .x2 (imm (8*i)), .SD .x2 .x0 (imm (8*i))]) ++
  [.SD .x2 .x0 104, .ADDI .x2 .x2 112] ++
  ((Crypto.Sha2.cleared.filter (fun r => ![.x10, .x11, .x12, .x13].contains r)).map
    fun r => .ADDI r .x0 0), .ret]

private def cleanup : Part := .seq [.asm (wipe .x19 .x20), .asm leaveValues]

private def failed : Part := .seq [
  .asm (block [.ADDI .x11 .x0 0, .ADDI .x12 .x0 0, .ADDI .x13 .x0 0]), cleanup]

private def errorOwned (status : Nat) : Part := .seq [
  .asm (block [.ADDI .x10 .x0 (imm status)]), failed]

private def rejectOwned (c : SAsm.Cond) (status : Nat) : Part :=
  .ite c (errorOwned status) (.asm empty)

/-- s0=base,s1=cursor,s2=remaining,s3=work,s4=work bytes,s5=kind,s6=data offset,
s7=data length,s8=seen flags,s9=group depth,s10=field,s11=wire. -/
private def validate : SAsm.Stmt := sequence [
  block [.SRLI .x5 .x11 61], reject (.ne .x5 .x0) 2,
  reject (.eq .x11 .x0) 7,
  block [.SLLI .x29 .x11 3], reject (.ltu .x13 .x29) 5,
  range .x10 .x11, range .x12 .x29,
  block [.ANDI .x5 .x12 7], reject (.ne .x5 .x0) 4,
  stackCheck 112,
  block [.ADDI .x28 .x2 (-112), .ADDI .x31 .x0 112],
  disjoint .x10 .x11 .x12 .x29,
  disjoint .x10 .x11 .x28 .x31,
  disjoint .x12 .x29 .x28 .x31]

private def setup : SAsm.Stmt := sequence [validate, enter,
  block [.ADDI .x8 .x10 0, .ADDI .x9 .x10 0, .ADDI .x18 .x11 0,
    .ADDI .x19 .x12 0, .ADDI .x20 .x29 0, .ADDI .x21 .x0 0,
    .ADDI .x22 .x0 0, .ADDI .x23 .x0 0, .ADDI .x24 .x0 0, .ADDI .x25 .x0 0]]

private def varint : Part := .seq [
  .asm (block [.ADDI .x10 .x9 0, .ADDI .x11 .x18 0]), .call 0,
  .ite (.ne .x10 .x0) failed (.asm empty),
  .asm (block [.ADD .x9 .x9 .x12, .SUB .x18 .x18 .x12])]

private def skipBytes (count : Reg) : Part := .seq [
  rejectOwned (.ltu .x18 count) 1,
  .asm (block [.ADD .x9 .x9 count, .SUB .x18 .x18 count])]

private def integer : Part := .seq [varint,
  .ite (.eq .x25 .x0) (.seq [
    .asm (block [.ADDI .x7 .x0 1]),
    .ite (.eq .x26 .x7) (.asm (block [.ADDI .x21 .x11 0, .ORI .x24 .x24 1]))
      (.asm empty)]) (.asm empty)]

private def bytes : Part := .seq [varint, rejectOwned (.ltu .x18 .x11) 1,
  .ite (.eq .x25 .x0) (.seq [
    .asm (block [.ADDI .x7 .x0 2]),
    .ite (.eq .x26 .x7) (.asm (block [
      .SUB .x22 .x9 .x8, .ADDI .x23 .x11 0, .ORI .x24 .x24 2])) (.asm empty)])
    (.asm empty),
  skipBytes .x11]

private def startGroup : Part := .seq [
  .asm (block [.SLLI .x7 .x25 3]), rejectOwned (.geu .x7 .x20) 5,
  .asm (block [.ADD .x5 .x19 .x7, .SD .x5 .x26 0, .ADDI .x25 .x25 1])]

private def endGroup : Part := .seq [
  rejectOwned (.eq .x25 .x0) 6,
  .asm (block [.ADDI .x25 .x25 (-1), .SLLI .x7 .x25 3,
    .ADD .x5 .x19 .x7, .LD .x6 .x5 0]),
  rejectOwned (.ne .x6 .x26) 6]

private def fixed (n : Nat) : Part := .seq [
  .asm (block [.ADDI .x11 .x0 (imm n)]), skipBytes .x11]

private def dispatch : Part :=
  ([(0, integer), (1, fixed 8), (2, bytes), (3, startGroup), (4, endGroup),
    (5, fixed 4)] : List (Nat × Part)).foldr (fun (n, body) rest =>
      .seq [.asm (block [.ADDI .x7 .x0 (imm n)]), .ite (.eq .x27 .x7) body rest])
    (errorOwned 6)

private def field : Part := .seq [varint,
  .asm (block [.SRLI .x5 .x11 32]), rejectOwned (.ne .x5 .x0) 6,
  .asm (block [.SRLI .x26 .x11 3, .ANDI .x27 .x11 7]),
  rejectOwned (.eq .x26 .x0) 6, dispatch]

private def complete : Part := .seq [
  rejectOwned (.ne .x25 .x0) 1,
  .asm (block [.ADDI .x7 .x0 3]), rejectOwned (.ne .x24 .x7) 7,
  .asm (block [.ADDI .x7 .x0 1]),
  .ite (.ne .x21 .x7) (.seq [.asm (block [.ADDI .x7 .x0 2]),
    rejectOwned (.ne .x21 .x7) 8]) (.asm empty),
  .asm (block [.ADDI .x7 .x21 31]), rejectOwned (.ne .x23 .x7) 9,
  .asm (block [.ADDI .x10 .x0 0, .ADDI .x11 .x21 0,
    .ADDI .x12 .x22 0, .ADDI .x13 .x23 0]), cleanup]

/-- a0=input,a1=length,a2=work,a3=capacity. Required work=8*length, stack=112.
Returns a0=status,a1=kind,a2=data offset,a3=data length. Failure clears results.
Unknown fields/groups are skipped; repeated singular fields use the last value.
Work is 8-aligned and disjoint from input/stack; used work/frame are wiped on
content returns. Empty input fails without accessing pointers. Length<2^61.
Mapping, lifetime, permissions and separation from code are caller preconditions. -/
def decode : Except String SAsm.Stmt := program (.seq [
  .asm setup, .loop (.ne .x18 .x0) field, complete]) [.asm Codec.ProtobufVarint.decode]

private def idValidate : SAsm.Stmt := sequence [
  block [.ADDI .x7 .x0 1],
  .ite (.ne .x10 .x7) (sequence [block [.ADDI .x7 .x0 2],
    reject (.ne .x10 .x7) 8]) empty,
  block [.ADDI .x7 .x10 31], reject (.ne .x12 .x7) 9,
  block [.ADDI .x29 .x12 6], reject (.ltu .x14 .x29) 5,
  range .x11 .x12, range .x13 .x29, disjoint .x11 .x12 .x13 .x29]

/-- a0=kind(1 Ed25519/2 secp256k1),a1=key,a2=length,a3=out,a4=capacity.
Returns a0=status,a1=written(38/39). Canonical protobuf in an identity multihash.
No stack/work; validates before any access. Does not prove curve-key validity. -/
def peerId : SAsm.Stmt := sequence [idValidate,
  block [.SB .x13 .x0 0, .ADDI .x5 .x12 4, .SB .x13 .x5 1,
    .ADDI .x5 .x0 8, .SB .x13 .x5 2, .SB .x13 .x10 3,
    .ADDI .x5 .x0 18, .SB .x13 .x5 4, .SB .x13 .x12 5, .ADDI .x30 .x13 6],
  copy .x30 .x11 .x12,
  block ([.ADDI .x11 .x29 0] ++
    ((Crypto.Sha2.cleared.filter (· != .x11)).map fun r => .ADDI r .x0 0)), .ret]

end Libp2pAsm.Asm.Identity.PublicKey
