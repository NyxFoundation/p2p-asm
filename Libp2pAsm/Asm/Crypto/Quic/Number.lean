import Libp2pAsm.Asm.Crypto.Quic.Common

namespace Libp2pAsm.Asm.Crypto.Quic
open Rv64 Util

/-- x11=IV, x12=PN, x13=out, prevalidated. No secret-dependent addressing.
The first four bytes are unchanged; all eight PN bytes are used. -/
def nonceBody : SAsm.Stmt := block <|
  (List.range 4).flatMap (fun i => [.LBU .x5 .x11 (imm i), .SB .x13 .x5 (imm i)]) ++
  (List.range 8).flatMap (fun i => [.LBU .x5 .x11 (imm (4+i)),
    .SRLI .x6 .x12 (BitVec.ofNat 6 (8*(7-i))), .XOR .x5 .x5 .x6, .SB .x13 .x5 (imm (4+i))])

/-- Descriptor: IV pointer, full PN, output pointer, output capacity. 32 bytes.
Status 2 number, 4 ranges/alignment/overlap, 5 capacity. No stack/workspace. -/
def nonce : SAsm.Stmt := sequence [descriptor 32,
  block [.LD .x12 .x10 8, .SRLI .x5 .x12 62], reject (.ne .x5 .x0) 2,
  block [.LD .x13 .x10 24], capacity .x13 12,
  spans 32 0 [fixed 0 12, fixed 16 12],
  block [.LD .x11 .x10 0, .LD .x13 .x10 16], nonceBody, finish 0]

/-- x11=expected in 0..2^62, x12=truncated, x13=PN bytes 1..4.
Returns candidate in x14; x5..x7 scratch. Arithmetic stays below 2^63.
The final candidate MUST be range-checked before use. -/
def reconstructBody : SAsm.Stmt := sequence [
  block [.SLLI .x5 .x13 3, .ADDI .x6 .x0 1, .SLL .x6 .x6 .x5,
    .ADDI .x7 .x6 (-1), .XORI .x7 .x7 (-1), .AND .x14 .x11 .x7,
    .OR .x14 .x14 .x12, .SRLI .x7 .x6 1, .ADD .x5 .x14 .x7],
  .ite (.geu .x11 .x5) (sequence [
    block (load .x5 (2^62) ++ [.SUB .x5 .x5 .x6]),
    .ite (.ltu .x14 .x5) (block [.ADD .x14 .x14 .x6]) empty])
    (sequence [block [.ADD .x5 .x11 .x7],
      .ite (.ltu .x5 .x14) (.ite (.geu .x14 .x6)
        (block [.SUB .x14 .x14 .x6]) empty) empty])]

/-- Descriptor: expected, truncated, byte count, output pointer, capacity.
Output is LE64 PN. expected=2^62 is legal metadata, but result must be <2^62. -/
def reconstruct : SAsm.Stmt := sequence [descriptor 40,
  block (load .x7 (2^62) ++ [.LD .x11 .x10 0]), reject (.ltu .x7 .x11) 2,
  block [.LD .x12 .x10 8, .LD .x13 .x10 16, .ADDI .x7 .x0 1],
  reject (.ltu .x13 .x7) 2, block [.ADDI .x7 .x0 4], reject (.ltu .x7 .x13) 2,
  block [.SLLI .x5 .x13 3, .SRL .x5 .x12 .x5], reject (.ne .x5 .x0) 2,
  block [.LD .x15 .x10 32], capacity .x15 8, spans 40 0 [fixed 24 8],
  reconstructBody, block [.SRLI .x5 .x14 62], reject (.ne .x5 .x0) 2,
  block [.LD .x15 .x10 24], storeLE .x15 .x14 0, finish 0]

end Libp2pAsm.Asm.Crypto.Quic
