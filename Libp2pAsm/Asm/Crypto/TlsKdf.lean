import Libp2pAsm.Asm.Crypto.Util

namespace Libp2pAsm.Asm.Crypto.TlsKdf
open Rv64 Util

private def validate : SAsm.Stmt := sequence [
  block (load .x7 65535), reject (.ltu .x7 .x14) 2,
  reject (.eq .x11 .x0) 8,
  block [.ADDI .x7 .x0 249], reject (.ltu .x7 .x11) 6,
  block [.ADDI .x7 .x0 255], reject (.ltu .x7 .x13) 7,
  block [.ADD .x29 .x11 .x13, .ADDI .x29 .x29 10],
  reject (.ltu .x16 .x29) 5,
  range .x10 .x11, range .x12 .x13, range .x15 .x29]

private def labelPrefix : SAsm.Stmt := block <|
  storeBE .x15 .x14 0 2 ++ [.ADDI .x7 .x11 6, .SB .x15 .x7 2] ++
  ([0x74, 0x6c, 0x73, 0x31, 0x33, 0x20].zipIdx.flatMap fun (b, i) =>
    [.ADDI .x7 .x0 (imm b), .SB .x15 .x7 (imm (3+i))])

/-- a0=label,a1=labelLen,a2=context,a3=contextLen,a4=requested output length,
a5=encoded output,a6=output capacity. Requires 10+labelLen+contextLen bytes.
Status 0=ok,2=uint16 length,6=long label,7=long context,8=empty label,5=resource,4=range.
No stack or workspace; s-registers/ra/sp/gp/tp preserved. Input/output unaligned.
Validation precedes all writes; no partial encoding on error. -/
def encodeLabel : SAsm.Stmt := sequence [validate, labelPrefix,
  block [.ADDI .x30 .x15 9], copy .x30 .x10 .x11,
  block [.ADD .x30 .x30 .x11, .SB .x30 .x13 0, .ADDI .x30 .x30 1],
  copy .x30 .x12 .x13, finish 0]

end Libp2pAsm.Asm.Crypto.TlsKdf
