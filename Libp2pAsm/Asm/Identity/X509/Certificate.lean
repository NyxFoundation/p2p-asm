import Libp2pAsm.Asm.Identity.X509.Names
import Libp2pAsm.Asm.Identity.X509.Keys
import Libp2pAsm.Asm.Identity.X509.Extensions

namespace Libp2pAsm.Asm.Identity.X509
open Rv64 Crypto.Util Crypto.Link

private def version : Part := .seq [expectNode 160,
  .asm (sequence [saveCursor 192, enterNode]), expectNode 2,
  .asm (sequence [endNode, block [.ADDI .x5 .x0 1], require (.eq .x26 .x5),
    block [.ADD .x5 .x9 .x25, .LBU .x5 .x5 0, .ADDI .x6 .x0 2],
    require (.eq .x5 .x6), restoreCursor 192])]

private def tbsBody : Part := .seq [
  version, expectNode 2,
  .asm (sequence [block [.ADDI .x5 .x0 20], require (.geu .x5 .x26), unsignedInteger]),
  expectNode 48, algorithm 1 88, expectNode 48, .call 4,
  expectNode 48, Keys.times, expectNode 48, .call 4,
  expectNode 48, Keys.publicKey,
  expectNode 163, .asm endNode, Extensions.all]

private def commit : SAsm.Stmt := sequence [
  block [.ADDI .x10 .x19 0, .ADDI .x11 .x20 0, .ADDI .x12 .x0 168],
  copy .x10 .x11 .x12, block [.ADDI .x10 .x0 0], cleanup]

private def root : Part := .seq [
  .asm (sequence [preflight, setup]), .call 7, expectNode 48,
  .asm (sequence [endNode, enterNode]), expectNode 48,
  .asm (sequence [saveSpan 0, saveCursor 176, enterNode]), tbsBody,
  .asm (restoreCursor 176), expectNode 48, algorithm 1 432,
  .asm (sequence [block [.LD .x5 .x20 88, .LD .x6 .x20 432],
    require (.eq .x5 .x6) 8]),
  expectNode 3, .asm (sequence [endNode, bitString, saveSpan 96 true, commit])]

/-- a0=64-byte descriptor: input,length,output,capacity,work,workCapacity,
certificateByteLimit,operationBudget. Output is21 LE64 words (168 bytes);
work is512+4*length bytes, stack144. No partial output on error.
Views are offsets, not pointers. No cryptographic authentication is claimed. -/
def certificate : Except String SAsm.Stmt :=
  program root [.asm Codec.Der.decode, .asm Algorithm.signature,
    .asm Algorithm.publicKey, .asm Time.decode, Names.parseName,
    Names.parseAttribute, Extensions.one, .asm handlerAddress]

end Libp2pAsm.Asm.Identity.X509
