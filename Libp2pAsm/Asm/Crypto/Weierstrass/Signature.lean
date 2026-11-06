import Libp2pAsm.Asm.Crypto.Weierstrass.Nonce

namespace Libp2pAsm.Asm.Crypto.Weierstrass
open Rv64 Util Link
open Spec.Crypto.Weierstrass (Curve)

/-- Public DER integer parser. s6=source,s7=length,s8=32-byte destination.
No input-dependent accesses are hidden: all DER/signature bytes are public.
Bounds are established by parseDER before this helper. -/
def parseInteger : Part := .seq [
  .asm (block [.LBU .x5 .x24 0, .ADDI .x6 .x0 128]), failWork (.geu .x5 .x6) 6,
  .asm (block [.ADDI .x6 .x0 1]),
  .ite (.ltu .x6 .x25) (.ite (.eq .x5 .x0) (.seq [
    .asm (block [.LBU .x5 .x24 1, .ADDI .x6 .x0 128]), failWork (.ltu .x5 .x6) 6,
    .asm (block [.ADDI .x24 .x24 1, .ADDI .x25 .x25 (-1)])]) (.asm empty)) (.asm empty),
  .asm (block [.ADDI .x5 .x0 33]), failWork (.geu .x25 .x5) 6,
  .asm (block [.ADDI .x5 .x0 32, .SUB .x5 .x5 .x25, .ADD .x26 .x26 .x5]),
  .asm (copy .x26 .x24 .x25)]

/-- Strict DER: shortest one-byte lengths; exactly two positive, minimal INTEGERs;
no trailing data. Stages compact bytes at864/896 before canonical scalar checks. -/
def parseDER : Part := .seq [
  .asm (block [.LD .x23 .x9 48, .LD .x27 .x9 56, .LBU .x5 .x23 0, .ADDI .x6 .x0 48]),
  failWork (.ne .x5 .x6) 6,
  .asm (block [.LBU .x5 .x23 1, .ADDI .x6 .x27 (-2)]), failWork (.ne .x5 .x6) 6,
  .asm (block [.LBU .x5 .x23 2, .ADDI .x6 .x0 2]), failWork (.ne .x5 .x6) 6,
  .asm (block [.LBU .x22 .x23 3, .ADDI .x5 .x22 (-1), .ADDI .x6 .x0 33]),
  failWork (.geu .x5 .x6) 6,
  .asm (block [.ADDI .x5 .x22 6]), failWork (.ltu .x27 .x5) 6,
  .asm (block [.ADD .x26 .x23 .x22, .LBU .x5 .x26 4, .ADDI .x6 .x0 2]),
  failWork (.ne .x5 .x6) 6,
  .asm (block [.LBU .x27 .x26 5, .ADDI .x5 .x27 (-1), .ADDI .x6 .x0 33]),
  failWork (.geu .x5 .x6) 6,
  .asm (block [.ADD .x5 .x22 .x27, .ADDI .x5 .x5 6, .LD .x6 .x9 56]),
  failWork (.ne .x5 .x6) 6,
  .asm (block [.ADDI .x24 .x23 4, .ADDI .x25 .x22 0, .ADDI .x26 .x8 864]), parseInteger,
  .asm (block [.ADD .x24 .x23 .x22, .ADDI .x24 .x24 6,
    .ADDI .x25 .x27 0, .ADDI .x26 .x8 896]), parseInteger,
  .asm (block [.ADDI .x11 .x8 864]), .asm (decode .x8 .x11 64 0),
  .asm (decode .x8 .x11 96 32)]

def parseSignature (c : Curve) (compact lowS : Bool) : Part := .seq [
  (if compact then .seq [.asm (block [.LD .x11 .x9 48]),
    .asm (decode .x8 .x11 64 0), .asm (decode .x8 .x11 96 32)] else parseDER),
  .asm (canonical .x8 64 c.order .x22 true), failWork (.eq .x22 .x0) 6,
  .asm (canonical .x8 96 c.order .x22 true), failWork (.eq .x22 .x0) 6,
  if lowS then .seq [.asm (canonical .x8 96 (c.order/2+1) .x22), failWork (.eq .x22 .x0) 6]
    else .asm empty]

/-- Fixed-access length scan of32 bytes. Outputs signed DER width in result.
All-zero input yields width1 (zero INTEGER). No secret-indexed loads. -/
def integerWidth (offset : Nat) (result : Reg) : SAsm.Stmt := sequence [
  block [.ADDI .x5 .x8 (imm offset), .ADDI .x6 .x0 32, .ADDI result .x0 1],
  .loop (.ne .x6 .x0) (block [.LBU .x7 .x5 0, .SRLI .x28 .x7 7,
    .ADD .x28 .x28 .x6, .SLTU .x29 .x0 .x7, .SLTU .x30 result .x28,
    .AND .x29 .x29 .x30, .SUB .x29 .x0 .x29,
    .XOR .x28 .x28 result, .AND .x28 .x28 .x29, .XOR result result .x28,
    .ADDI .x5 .x5 1, .ADDI .x6 .x6 (-1)])]

/-- Add value masked by (position==index) into accumulator a4; clobbers t0/t1.
Positions may depend on signature bytes, but never address memory or branch. -/
def derByte (position value : Reg) : SAsm.Stmt := block [
  .XOR .x5 .x10 position, .SLTU .x5 .x0 .x5, .ADDI .x5 .x5 (-1),
  .AND .x6 .x5 value, .OR .x14 .x14 .x6]

/-- Scan every32-byte source for each output byte; no secret-dependent indices. -/
def derPayload (source : Nat) (endPos : Reg) : SAsm.Stmt := sequence [
  block [.ADDI .x11 .x8 (imm source), .ADDI .x12 endPos (-32), .ADDI .x13 .x0 32],
  .loop (.ne .x13 .x0) (sequence [block [.LBU .x15 .x11 0], derByte .x12 .x15,
    block [.ADDI .x11 .x11 1, .ADDI .x12 .x12 1, .ADDI .x13 .x13 (-1)]])]

/-- Output record at704: LE64 DER length, then72 bytes with zero padding.
Every output position scans all signature bytes. r/s are ordinary limbs64/96.
The fixed80-byte record can be committed atomically without leaking DER widths
through branches or addresses. Published DER is record[8,8+length). -/
def encodeDER : Part := .asm <| sequence [
  encode .x8 .x8 864 64, encode .x8 .x8 896 96,
  integerWidth 864 .x23, integerWidth 896 .x24,
  block [.ADD .x25 .x23 .x24, .ADDI .x25 .x25 6, .SD .x8 .x25 704,
    .ADDI .x26 .x23 4, .ADDI .x27 .x26 2,
    .ADDI .x10 .x0 0, .ADDI .x16 .x8 712, .ADDI .x17 .x0 72],
  .loop (.ltu .x10 .x17) (sequence [
    block [.ADDI .x14 .x0 0, .ADDI .x12 .x0 0, .ADDI .x15 .x0 48], derByte .x12 .x15,
    block [.ADDI .x12 .x0 1, .ADDI .x15 .x25 (-2)], derByte .x12 .x15,
    block [.ADDI .x12 .x0 2, .ADDI .x15 .x0 2], derByte .x12 .x15,
    block [.ADDI .x12 .x0 3], derByte .x12 .x23,
    block [.ADDI .x15 .x0 2], derByte .x26 .x15,
    block [.ADDI .x12 .x26 1], derByte .x12 .x24,
    derPayload 864 .x26, derPayload 896 .x25,
    block [.SB .x16 .x14 0, .ADDI .x16 .x16 1, .ADDI .x10 .x10 1]])]

end Libp2pAsm.Asm.Crypto.Weierstrass
