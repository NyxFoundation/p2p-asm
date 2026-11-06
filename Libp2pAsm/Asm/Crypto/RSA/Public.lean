import Libp2pAsm.Asm.Crypto.RSA.Abi

namespace Libp2pAsm.Asm.Crypto.RSA
open Rv64 Util Link

/-- Equal-length BE compare a1<a2, length a3. No early value truncation. -/
def lessBE : SAsm.Stmt := sequence [
  block [.ADDI .x5 .x0 0, .ADDI .x14 .x0 0],
  .loop (.ltu .x5 .x13) (sequence [
    block [.SUB .x6 .x13 .x5, .ADDI .x6 .x6 (-1),
      .ADD .x7 .x11 .x6, .LBU .x28 .x7 0, .ADD .x7 .x12 .x6, .LBU .x29 .x7 0],
    .ite (.ne .x28 .x29) (block [.SLTU .x14 .x28 .x29]) empty,
    block [.ADDI .x5 .x5 1]])]

def keyContent : SAsm.Stmt := sequence [
  block [.LD .x11 .x9 0, .LD .x12 .x9 8, .LBU .x5 .x11 0],
  failWork (.eq .x5 .x0) 1,
  block [.ADD .x6 .x11 .x12, .LBU .x7 .x6 (-1), .ANDI .x7 .x7 1],
  failWork (.eq .x7 .x0) 1,
  block [.ADDI .x26 .x12 (-1), .SLLI .x26 .x26 3],
  .loop (.ne .x5 .x0) (block [.SRLI .x5 .x5 1, .ADDI .x26 .x26 1]),
  block [.ADDI .x7 .x0 3], failWork (.ltu .x26 .x7) 1,
  block [.SD .x25 .x26 848,
    .LD .x11 .x9 16, .LD .x13 .x9 24, .LBU .x5 .x11 0],
  failWork (.eq .x5 .x0) 1,
  block [.ADD .x6 .x11 .x13, .LBU .x6 .x6 (-1), .ANDI .x7 .x6 1],
  failWork (.eq .x7 .x0) 1,
  block [.ADDI .x7 .x0 1],
  .ite (.eq .x13 .x7) (sequence [block [.ADDI .x7 .x0 3], failWork (.ltu .x6 .x7) 1]) empty,
  block [.LD .x12 .x9 8],
  .ite (.eq .x13 .x12) (sequence [block [.LD .x12 .x9 0], lessBE,
    failWork (.eq .x14 .x0) 1]) empty,
  block [.LD .x7 .x9 104], failWork (.ltu .x26 .x7) 6,
  block [.LD .x11 .x9 32, .LD .x12 .x9 0, .LD .x13 .x9 8], lessBE,
  failWork (.eq .x14 .x0) 2]

def loadOperands : SAsm.Stmt := sequence [
  block [.ADDI .x10 .x8 0, .LD .x11 .x9 0, .LD .x12 .x9 8], decode,
  block [.ADDI .x10 .x20 0, .LD .x11 .x9 32], decode,
  block [.LD .x5 .x8 0, .ADDI .x6 .x0 1, .ADDI .x7 .x0 2],
  block ((List.range 5).flatMap fun _ => [
    .MUL .x28 .x5 .x6, .SUB .x28 .x7 .x28, .MUL .x6 .x6 .x28,
    .SLLI .x6 .x6 32, .SRLI .x6 .x6 32]),
  block [.SUB .x6 .x0 .x6, .SLLI .x6 .x6 32, .SRLI .x6 .x6 32,
    .SD .x25 .x6 856, .ADDI .x5 .x26 (-1), .SRLI .x6 .x5 5,
    .SLLI .x6 .x6 3, .ADD .x6 .x22 .x6, .ANDI .x5 .x5 31,
    .ADDI .x7 .x0 1, .SLL .x7 .x7 .x5, .SD .x6 .x7 0,
    .SLLI .x5 .x18 6, .SUB .x26 .x5 .x26, .ADDI .x26 .x26 1]]

/-- Internal callee indices: 0 Montgomery, 1 double, 2 whole SHA256. -/
def mont (dst a b : Reg) : Part := .seq [
  .asm (block [.ADDI .x10 dst 0, .ADDI .x11 a 0, .ADDI .x12 b 0,
    .ADDI .x13 .x8 0, .ADDI .x14 .x18 0, .LD .x15 .x25 856,
    .ADDI .x16 .x23 0, .ADDI .x17 .x24 0]), .call 0]

def precompute : Part := .seq [
  .loop (.ne .x26 .x0) (.seq [
    .asm (block [.ADDI .x10 .x22 0, .ADDI .x11 .x8 0,
      .ADDI .x12 .x18 0, .ADDI .x13 .x24 0]), .call 1,
    .asm (block [.ADDI .x26 .x26 (-1)])]),
  .asm (block [.ADDI .x5 .x0 1, .SD .x21 .x5 0]),
  mont .x20 .x20 .x22, mont .x21 .x21 .x22]

/-- Public variable-time square-and-multiply. All exponent bytes are consumed;
no assumption e=65537, no window or integer-width truncation. -/
def exponentiate : Part := .seq [
  .asm (block [.ADDI .x26 .x0 0, .LD .x27 .x9 24]),
  .loop (.ltu .x26 .x27) (.seq [
    .asm (block [.ADDI .x5 .x0 128, .SD .x25 .x5 864]),
    .loop (.ne .x5 .x0) (.seq [mont .x21 .x21 .x21,
      .asm (block [.LD .x5 .x25 864, .LD .x6 .x9 16,
        .ADD .x6 .x6 .x26, .LBU .x7 .x6 0, .AND .x7 .x7 .x5]),
      .ite (.ne .x7 .x0) (mont .x21 .x21 .x20) (.asm empty),
      .asm (block [.LD .x5 .x25 864, .SRLI .x5 .x5 1, .SD .x25 .x5 864])]),
    .asm (block [.ADDI .x26 .x26 1])]),
  .asm (wipe .x22 .x19), .asm (block [.ADDI .x5 .x0 1, .SD .x22 .x5 0]),
  mont .x21 .x21 .x22,
  .asm (block [.ADDI .x10 .x20 0, .ADDI .x11 .x21 0, .LD .x12 .x9 8]), .asm encode]

end Libp2pAsm.Asm.Crypto.RSA
