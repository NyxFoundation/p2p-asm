import Libp2pAsm.Asm.Codec.Abi

namespace Libp2pAsm.Asm.Codec.QuicVarint

open Rv64

private def setWidth (width tag : BitVec 12) : SAsm.Stmt :=
  .block [.ADDI .x5 .x0 width, .ADDI .x7 .x0 tag]

private def selectWidth : SAsm.Stmt :=
  sequence [
    .block [.SRLI .x6 .x10 6],
    .ite (.eq .x6 .x0) (setWidth 1 0)
      (sequence [
        .block [.SRLI .x6 .x10 14],
        .ite (.eq .x6 .x0) (setWidth 2 64)
          (sequence [
            .block [.SRLI .x6 .x10 30],
            .ite (.eq .x6 .x0) (setWidth 4 128) (setWidth 8 192)])])]

private def emitByte : SAsm.Stmt :=
  .block [
    .SRL .x28 .x10 .x6, .ANDI .x28 .x28 255, .OR .x28 .x28 .x7,
    .SB .x11 .x28 0, .ADDI .x11 .x11 1, .ADDI .x5 .x5 (-1),
    .ADDI .x6 .x6 (-8), .ADDI .x7 .x0 0]

private def encodeBody : SAsm.Stmt :=
  sequence [
    selectWidth,
    .ite (.ltu .x12 .x5) (returnError 1)
      (sequence [
        .block [.ADDI .x31 .x5 0, .ADDI .x6 .x5 (-1), .SLLI .x6 .x6 3],
        .loop (.ne .x5 .x0) emitByte, encodeSuccess])]

/-- a0=value, a1=output pointer, a2=capacity. No writes occur on errors. -/
def encode : SAsm.Stmt :=
  sequence [
    .block [.SRLI .x5 .x10 62],
    .ite (.ne .x5 .x0) (returnError 2) encodeBody]

private def readTail : SAsm.Stmt :=
  .block [
    .SLLI .x28 .x28 8, .LBU .x29 .x10 0, .OR .x28 .x28 .x29,
    .ADDI .x10 .x10 1, .ADDI .x7 .x7 (-1)]

private def decodeBody : SAsm.Stmt :=
  sequence [
    .block [.LBU .x5 .x10 0, .SRLI .x7 .x5 6,
      .ADDI .x6 .x0 1, .SLL .x6 .x6 .x7],
    .ite (.ltu .x11 .x6) (returnError 1)
      (sequence [
        .block [.ANDI .x28 .x5 63, .ADDI .x10 .x10 1, .ADDI .x7 .x6 (-1)],
        .loop (.ne .x7 .x0) readTail, decodeSuccess])]

/-- a0=input pointer, a1=length. Legal non-minimal QUIC encodings are accepted. -/
def decode : SAsm.Stmt :=
  .ite (.eq .x11 .x0) (returnError 1) decodeBody

end Libp2pAsm.Asm.Codec.QuicVarint
