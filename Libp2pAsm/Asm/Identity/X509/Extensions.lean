import Libp2pAsm.Asm.Identity.X509.ExtensionValues

namespace Libp2pAsm.Asm.Identity.X509.Extensions
open Rv64 Crypto.Util Crypto.Link

private def comparePrevious : SAsm.Stmt := sequence [
  block [.LD .x14 .x12 8],
  .ite (.eq .x14 .x26) (sequence [
    block [.LD .x13 .x12 0, .ADD .x13 .x9 .x13, .ADD .x15 .x9 .x25],
    .loop (.ne .x14 .x0) (sequence [tick,
      block [.LBU .x5 .x13 0, .LBU .x6 .x15 0],
      .ite (.ne .x5 .x6) (block [.ADDI .x14 .x0 0, .ADDI .x16 .x0 1])
        (block [.ADDI .x13 .x13 1, .ADDI .x15 .x15 1, .ADDI .x14 .x14 (-1)])]),
    require (.ne .x16 .x0) 9]) empty]

private def uniqueOid : SAsm.Stmt := sequence [
  block [.LD .x10 .x20 424, .ADDI .x11 .x0 0, .ADDI .x12 .x20 512],
  .loop (.ltu .x11 .x10) (sequence [tick, block [.ADDI .x16 .x0 0],
    comparePrevious, block [.ADDI .x11 .x11 1, .ADDI .x12 .x12 16]]),
  block [.SRLI .x5 .x18 2], require (.ltu .x10 .x5) 12,
  block [.SD .x12 .x25 0, .SD .x12 .x26 8, .ADDI .x10 .x10 1,
    .SD .x20 .x10 424, .SD .x20 .x25 256, .SD .x20 .x26 264]]

/-- Temporarily select saved OID content for comparison, retaining extnValue. -/
private def identify (bytes : List Nat) : SAsm.Stmt := sequence [
  block [.SD .x20 .x25 288, .SD .x20 .x26 296,
    .LD .x25 .x20 256, .LD .x26 .x20 264],
  equalBytes bytes,
  block [.LD .x25 .x20 288, .LD .x26 .x20 296]]

private def selectedValue : Part :=
  [([43,6,1,4,1,131,162,90,1,1], ExtensionValues.signedKey),
   ([85,29,15], ExtensionValues.keyUsage),
   ([85,29,19], ExtensionValues.basicConstraints),
   ([85,29,37], ExtensionValues.extendedUsage)].foldr
    (fun (id, body) otherwise => .seq [.asm (identify id),
      .ite (.ne .x11 .x0) body otherwise])
    (.asm (sequence [block [.LD .x5 .x20 272], require (.eq .x5 .x0) 10]))

/-- Internal callee6, sharing cursor registers and owning16 stack bytes. -/
def one : Part := .seq [
  .asm (sequence [helperEnter, saveCursor 208, enterNode]),
  expectNode 6, .asm (sequence [validOid, uniqueOid]), nextNode,
  .asm (block [.SD .x20 .x0 272, .ADDI .x5 .x0 1]),
  .ite (.eq .x11 .x5) (.seq [
    .asm (sequence [boolean, block [.SD .x20 .x11 272]]), expectNode 4])
    (.asm (sequence [block [.ADDI .x5 .x0 4], require (.eq .x11 .x5)])),
  .asm endNode, selectedValue,
  .asm (sequence [restoreCursor 208, helperLeave])]

def all : Part := .seq [
  .asm enterNode, expectNode 48,
  .asm (sequence [endNode, enterNode, require (.ne .x26 .x0) 11]),
  .loop (.ne .x21 .x22) (.seq [expectNode 48, .call 6]),
  .asm (sequence [
    block [.LD .x5 .x20 416], require (.ne .x5 .x0) 11,
    block [.LD .x5 .x20 400, .LD .x6 .x20 408, .MUL .x5 .x5 .x6,
      .SD .x20 .x5 160]])]

end Libp2pAsm.Asm.Identity.X509.Extensions
