import Libp2pAsm.Asm.Identity.X509.Common

namespace Libp2pAsm.Asm.Identity.X509.ExtensionValues
open Rv64 Crypto.Util Crypto.Link

def signedKey : Part := .seq [
  .asm enterNode, expectNode 48, .asm (sequence [endNode, enterNode]),
  expectNode 4, .asm (saveSpan 128 true),
  expectNode 4, .asm (sequence [saveSpan 144 true, endNode,
    block [.ADDI .x5 .x0 1, .SD .x20 .x5 416]])]

private def keyBits : SAsm.Stmt := sequence [
  block [.ADDI .x5 .x0 1], require (.geu .x26 .x5),
  block [.ADDI .x5 .x0 4], require (.ltu .x26 .x5),
  block [.ADD .x10 .x9 .x25, .LBU .x11 .x10 0, .ADDI .x5 .x0 8],
  require (.ltu .x11 .x5),
  block [.SD .x20 .x0 400, .ADDI .x5 .x0 1],
  .ite (.eq .x26 .x5) (require (.eq .x11 .x0)) (sequence [
    block [.ADD .x12 .x10 .x26, .LBU .x12 .x12 (-1)],
    require (.ne .x12 .x0),
    block [.ADDI .x5 .x0 1, .SLL .x5 .x5 .x11, .ADDI .x5 .x5 (-1), .AND .x6 .x12 .x5],
    require (.eq .x6 .x0),
    block [.SRL .x6 .x12 .x11, .ANDI .x6 .x6 1], require (.ne .x6 .x0),
    block [.ADDI .x5 .x0 3],
    .ite (.eq .x26 .x5) (sequence [
      block [.ADDI .x5 .x0 7], require (.eq .x11 .x5),
      block [.ADDI .x5 .x0 128], require (.eq .x12 .x5)]) empty,
    block [.LBU .x5 .x10 1, .SRLI .x5 .x5 7, .SD .x20 .x5 400]])]

def keyUsage : Part := .seq [
  .asm enterNode, expectNode 3, .asm (sequence [endNode, keyBits])]

def basicConstraints : Part := .seq [
  .asm enterNode, expectNode 48, .asm (sequence [endNode, enterNode]),
  .ite (.ne .x21 .x22) (.seq [
    expectNode 1, .asm boolean,
    .ite (.ne .x21 .x22) (.seq [
      .asm (require (.ne .x11 .x0)), expectNode 2, .asm unsignedInteger]) (.asm empty),
    .asm endNode]) (.asm empty)]

private def usageOid (bytes : List Nat) (flag : Nat) : SAsm.Stmt := sequence [
  equalBytes bytes,
  .ite (.ne .x11 .x0) (block [
    .LD .x5 .x20 408, .ORI .x5 .x5 (imm flag), .SD .x20 .x5 408]) empty]

def extendedUsage : Part := .seq [
  .asm enterNode, expectNode 48,
  .asm (sequence [endNode, enterNode, require (.ne .x26 .x0), block [.SD .x20 .x0 408]]),
  .loop (.ne .x21 .x22) (.seq [
    expectNode 6, .asm (sequence [validOid,
      usageOid [85,29,37,0] 3,
      usageOid [43,6,1,5,5,7,3,1] 1,
      usageOid [43,6,1,5,5,7,3,2] 2])])]

end Libp2pAsm.Asm.Identity.X509.ExtensionValues
