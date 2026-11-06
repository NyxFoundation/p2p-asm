import Libp2pAsm.Asm.Crypto.Weierstrass.FormulaP256
import Libp2pAsm.Asm.Crypto.Weierstrass.FormulaK256
import Libp2pAsm.Asm.Crypto.HMAC

namespace Libp2pAsm.Asm.Crypto.Weierstrass
open Rv64 Util Link
open Spec.Crypto.Weierstrass (Curve)

/-- Complete homogeneous coordinates (X:Y:Z), affine=(X/Z,Y/Z).
Infinity=(0:R:0). Inputs must be valid projective points, not all zero.
a0=out96,a1=P96,a2=Q96, arbitrary aliasing, aligned.
Owns 672-byte data frame +112 save frame +112 nested field frame=896 bytes.
Layout: P[0,96),Q[96,192),six temps[192,384),result[384,480),
extra temps[480,576),bR[576,608),3R[608,640),21R[640,672). -/
def pointAdd (c : Curve) : Part := .seq [
  .asm enter, .asm (block [.ADDI .x2 .x2 (-672), .ADDI .x8 .x2 0, .ADDI .x9 .x10 0]),
  .asm (wordsCopy .x8 .x11 0 0 12), .asm (wordsCopy .x8 .x12 96 0 12),
  .asm (constant .x8 576 (c.b*2^256 % c.prime)),
  .asm (constant .x8 608 (3*2^256 % c.prime)),
  .asm (constant .x8 640 (21*2^256 % c.prime)),
  (if c == .p256 then formulaP256 else formulaK256),
  .asm (wordsCopy .x9 .x8 0 384 12), .asm (zeroWords .x8 0 84),
  .asm (block [.ADDI .x2 .x2 672, .ADDI .x10 .x0 0]), .asm leave]

/-- a0=out96,a1=scalar32 LE,a2=point96, aligned, may alias.
Exactly 256 doubles, 256 complete adds, 256 masked selections.
Owns 320 data +112 save +896 nested point bytes =1328 bytes.
Layout: accumulator[0,96),candidate[96,192),point[192,288),scalar[288,320).
Zero/order scalar deliberately supported at this private arithmetic layer. -/
def pointMul (c : Curve) : Part := .seq [
  .asm enter, .asm (block [.ADDI .x2 .x2 (-320), .ADDI .x8 .x2 0,
    .ADDI .x9 .x10 0, .ADDI .x18 .x0 256]),
  .asm (wordsCopy .x8 .x11 288 0), .asm (wordsCopy .x8 .x12 192 0 12),
  .asm (zeroWords .x8 0 12), .asm (constant .x8 32 (2^256 % c.prime)),
  .loop (.ne .x18 .x0) (.seq [op 8 0 0 0, op 8 96 0 192,
    .asm (block [.ADDI .x18 .x18 (-1), .SRLI .x5 .x18 6, .SLLI .x5 .x5 3,
      .ADD .x5 .x8 .x5, .LD .x6 .x5 288, .SRL .x6 .x6 .x18,
      .ANDI .x6 .x6 1, .SUB .x19 .x0 .x6,
      .ADDI .x10 .x8 0, .ADDI .x11 .x8 96, .ADDI .x12 .x8 0]),
    .asm (maskSelect .x10 .x11 .x12 .x19 12)]),
  .asm (wordsCopy .x9 .x8 0 0 12), .asm (zeroWords .x8 0 40),
  .asm (block [.ADDI .x2 .x2 320, .ADDI .x10 .x0 0]), .asm leave]

/-- a0=out64,a1=projective96. Infinity maps to (0,0); caller must reject it.
Output is canonical ordinary limbs, ready for encode. Frame depth 624 bytes.
Data: point[0,96),inverse[96,128),ordinary one[128,160). -/
def toAffine : Part := .seq [
  .asm enter, .asm (block [.ADDI .x2 .x2 (-160), .ADDI .x8 .x2 0, .ADDI .x9 .x10 0]),
  .asm (wordsCopy .x8 .x11 0 0 12), .asm (constant .x8 128 1),
  op 6 96 64 64, op 0 0 0 96, op 0 32 32 96,
  op 0 0 0 128, op 0 32 32 128, .asm (wordsCopy .x9 .x8 0 0 8),
  .asm (zeroWords .x8 0 20),
  .asm (block [.ADDI .x2 .x2 160, .ADDI .x10 .x0 0]), .asm leave]

/-- HMAC's original local SHA index is rebased without changing the shared file. -/
def rebase : Part → Part
  | .call n => .call (n+11)
  | .asm s => .asm s
  | .seq ps => .seq (ps.map rebase)
  | .ite c a b => .ite c (rebase a) (rebase b)
  | .loop c b => .loop c (rebase b)

def callees (c : Curve) : List Part := fieldCallees c ++ [
  pointAdd c, pointMul c, toAffine, .asm (Whole.body .sha256), rebase HMAC.body,
  power c.prime ((c.prime+1)/4) 0]

end Libp2pAsm.Asm.Crypto.Weierstrass
