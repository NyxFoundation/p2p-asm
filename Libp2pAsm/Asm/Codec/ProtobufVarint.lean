import Libp2pAsm.Asm.Crypto.Util

namespace Libp2pAsm.Asm.Codec.ProtobufVarint
open Rv64 Crypto.Util

private def success : SAsm.Stmt := sequence [
  block ([.ADDI .x11 .x28 0, .ADDI .x12 .x6 0] ++
    ((Crypto.Sha2.cleared.filter (fun r => r != .x11 && r != .x12)).map
      fun r => .ADDI r .x0 0)), .ret]

private def byte : SAsm.Stmt := sequence [
  block [.LBU .x5 .x10 0, .ADDI .x31 .x0 9],
  .ite (.eq .x6 .x31) (sequence [
    block [.ADDI .x31 .x0 1], reject (.ltu .x31 .x5) 2]) empty,
  block [.ANDI .x29 .x5 127, .SLL .x30 .x29 .x7, .OR .x28 .x28 .x30,
    .ADDI .x6 .x6 1, .SRLI .x30 .x5 7],
  .ite (.eq .x30 .x0) success empty,
  block [.ADDI .x10 .x10 1, .ADDI .x11 .x11 (-1), .ADDI .x7 .x7 7]]

/-- a0=input,a1=available -> a0=status,a1=value,a2=consumed.
Accepts full uint64 and non-minimal protobuf encodings. Reads at most ten bytes;
failure clears results; no stack or writes. Checks range before reading.
Mapping/permissions and code separation remain caller preconditions. -/
def decode : SAsm.Stmt := sequence [
  range .x10 .x11,
  block [.ADDI .x6 .x0 0, .ADDI .x7 .x0 0, .ADDI .x28 .x0 0],
  .loop (.ne .x11 .x0) byte,
  finish 1]

end Libp2pAsm.Asm.Codec.ProtobufVarint
