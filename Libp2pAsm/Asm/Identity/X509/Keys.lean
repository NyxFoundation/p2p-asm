import Libp2pAsm.Asm.Identity.X509.Common

namespace Libp2pAsm.Asm.Identity.X509.Keys
open Rv64 Crypto.Util Crypto.Link

private def rsa : Part := .seq [
  .asm (sequence [saveCursor 208, enterNode]),
  expectNode 48, .asm (sequence [endNode, enterNode]),
  expectNode 2, .asm (saveSpan 56 true),
  expectNode 2, .asm (saveSpan 72 true),
  .asm (sequence [endNode,
    block [.LD .x25 .x20 56, .LD .x26 .x20 64], unsignedInteger, saveSpan 56 true,
    block [.LD .x25 .x20 72, .LD .x26 .x20 80], unsignedInteger, saveSpan 72 true,
    restoreCursor 208])]

def publicKey : Part := .seq [
  .asm (sequence [saveSpan 16, saveCursor 192, enterNode]),
  expectNode 48, algorithm 2 32,
  expectNode 3, .asm (sequence [endNode, bitString, saveSpan 40 true,
    block [.LD .x5 .x20 32, .ADDI .x6 .x0 3]]),
  .ite (.eq .x5 .x6) rsa (.asm (sequence [
    block [.ADDI .x6 .x0 1],
    .ite (.eq .x5 .x6)
      (sequence [block [.ADDI .x6 .x0 32], require (.eq .x26 .x6)])
      (sequence [block [.ADDI .x6 .x0 65], require (.eq .x26 .x6),
        block [.ADD .x6 .x9 .x25, .LBU .x6 .x6 0, .ADDI .x7 .x0 4],
        require (.eq .x6 .x7)])])),
  .asm (sequence [endNode, restoreCursor 192,
    block [.LD .x5 .x20 88, .LD .x6 .x20 32, .ADDI .x7 .x0 3],
    .ite (.geu .x5 .x7) (block [.ADDI .x5 .x0 3]) empty,
    require (.eq .x5 .x6) 8])]

def times : Part := .seq [
  .asm (sequence [saveCursor 192, enterNode]), nextNode,
  .asm (block [.SD .x20 .x11 304, .SD .x20 .x25 312, .SD .x20 .x26 320]),
  nextNode, .asm (sequence [endNode,
    block [.SD .x20 .x11 328, .SD .x20 .x25 336, .SD .x20 .x26 344,
      .LD .x11 .x20 304, .LD .x25 .x20 312, .LD .x26 .x20 320]]),
  calendar 112,
  .asm (block [.LD .x11 .x20 328, .LD .x25 .x20 336, .LD .x26 .x20 344]),
  calendar 120,
  .asm (sequence [restoreCursor 192,
    block [.LD .x5 .x20 112, .LD .x6 .x20 120, .SLT .x5 .x6 .x5],
    require (.eq .x5 .x0)])]

end Libp2pAsm.Asm.Identity.X509.Keys
