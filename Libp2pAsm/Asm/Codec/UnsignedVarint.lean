import Libp2pAsm.Asm.Codec.Abi

namespace Libp2pAsm.Asm.Codec.UnsignedVarint

open Rv64

private def countBytes : SAsm.Stmt :=
  sequence [
    .block [.ADDI .x5 .x10 0, .ADDI .x6 .x0 1, .ADDI .x7 .x0 128],
    .loop (.geu .x5 .x7) (.block [.SRLI .x5 .x5 7, .ADDI .x6 .x6 1]),
    .block [.ADDI .x31 .x6 0]]

private def emitByte : SAsm.Stmt :=
  sequence [
    .block [.ANDI .x28 .x10 127, .SRLI .x10 .x10 7],
    .ite (.ne .x10 .x0) (.block [.ORI .x28 .x28 128]) (.block []),
    .block [.SB .x11 .x28 0, .ADDI .x11 .x11 1, .ADDI .x6 .x6 (-1)]]

private def encodeBody : SAsm.Stmt :=
  sequence [
    countBytes,
    .ite (.ltu .x12 .x6) (returnError 1)
      (sequence [.loop (.ne .x6 .x0) emitByte, encodeSuccess])]

/-- a0=value, a1=output pointer, a2=capacity. Values are restricted to 63 bits. -/
def encode : SAsm.Stmt :=
  sequence [
    .block [.SRLI .x5 .x10 63],
    .ite (.ne .x5 .x0) (returnError 2) encodeBody]

private def finishDecode : SAsm.Stmt :=
  sequence [
    .block [.ADDI .x30 .x0 1],
    .ite (.ltu .x30 .x6)
      (.ite (.eq .x29 .x0) (returnError 3) decodeSuccess)
      decodeSuccess]

private def readByte : SAsm.Stmt :=
  sequence [
    .block [.LBU .x5 .x10 0, .ANDI .x29 .x5 127, .SLL .x30 .x29 .x7,
      .OR .x28 .x28 .x30, .ADDI .x6 .x6 1, .SRLI .x30 .x5 7],
    .ite (.eq .x30 .x0) finishDecode (.block []),
    .ite (.eq .x6 .x31) (returnError 2) (.block []),
    .block [.ADDI .x10 .x10 1, .ADDI .x11 .x11 (-1), .ADDI .x7 .x7 7]]

/-- a0=input pointer, a1=length. Read at most nine bytes and reject overlong forms. -/
def decode : SAsm.Stmt :=
  sequence [
    .block [.ADDI .x6 .x0 0, .ADDI .x7 .x0 0, .ADDI .x28 .x0 0, .ADDI .x31 .x0 9],
    .loop (.ne .x11 .x0) readByte,
    returnError 1]

end Libp2pAsm.Asm.Codec.UnsignedVarint
