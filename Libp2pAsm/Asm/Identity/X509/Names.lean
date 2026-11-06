import Libp2pAsm.Asm.Identity.X509.Strings

namespace Libp2pAsm.Asm.Identity.X509.Names
open Rv64 Crypto.Util Crypto.Link

/-- Compare adjacent full DER SET OF elements lexicographically. -/
private def ordered : SAsm.Stmt := sequence [
  block [.LD .x12 .x20 336, .LD .x13 .x20 344],
  .ite (.ne .x13 .x0) (sequence [
    block [.ADD .x10 .x9 .x12, .ADD .x11 .x9 .x23, .ADDI .x14 .x24 0],
    .loop (.ne .x13 .x0) (sequence [require (.ne .x14 .x0), tick,
      block [.LBU .x15 .x10 0, .LBU .x16 .x11 0], require (.geu .x16 .x15),
      .ite (.ltu .x15 .x16) (block [.ADDI .x13 .x0 0])
        (block [.ADDI .x10 .x10 1, .ADDI .x11 .x11 1,
          .ADDI .x13 .x13 (-1), .ADDI .x14 .x14 (-1)])])]) empty]

private def stringValue : SAsm.Stmt :=
  [(12, Strings.utf8), (18, Strings.ascii 18), (19, Strings.ascii 19),
    (22, Strings.ascii 22), (28, Strings.wide 4), (30, Strings.wide 2)].foldr
    (fun (tag, body) otherwise => sequence [
      block [.ADDI .x5 .x0 (imm tag)], .ite (.eq .x11 .x5) body otherwise]) empty

/-- Internal callee5. Shares the parser registers; owns16 bytes, not a public ABI. -/
def parseAttribute : Part := .seq [
  .asm (sequence [helperEnter,
    block [.SD .x20 .x23 352, .SD .x20 .x24 360], saveCursor 224, enterNode]),
  expectNode 6, .asm validOid, nextNode,
  .asm (sequence [endNode, stringValue,
    block [.LD .x23 .x20 352, .LD .x24 .x20 360], ordered,
    block [.SD .x20 .x23 336, .SD .x20 .x24 344], restoreCursor 224, helperLeave])]

private def rdn : Part := .seq [expectNode 49,
  .asm (sequence [require (.ne .x26 .x0), saveCursor 208, enterNode,
    block [.SD .x20 .x0 344]]),
  .loop (.ne .x21 .x22) (.seq [expectNode 48, .call 5]),
  .asm (restoreCursor 208)]

/-- Internal callee4; caller has consumed a Name SEQUENCE header. -/
def parseName : Part := .seq [
  .asm (sequence [helperEnter, saveCursor 192, enterNode]),
  .loop (.ne .x21 .x22) rdn,
  .asm (sequence [restoreCursor 192, helperLeave])]

end Libp2pAsm.Asm.Identity.X509.Names
