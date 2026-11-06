import Libp2pAsm.Asm.Crypto.Weierstrass.Field

/-! HACL* complete homogeneous projective formula, translated to canonical
Montgomery field calls. Copyright INRIA, CMU, Microsoft and HACL* contributors.
MIT: LICENSES/hacl-weierstrass.txt. See README for immutable provenance.
This port does not inherit the upstream verification proof. -/
namespace Libp2pAsm.Asm.Crypto.Weierstrass
open Link

def formulaK256 : Part := .seq [
    op 0 192 0 96,
    op 0 224 32 128,
    op 0 256 64 160,
    op 1 288 0 32,
    op 1 544 96 128,
    op 0 288 288 544,
    op 1 544 192 224,
    op 2 288 288 544,
    op 1 320 32 64,
    op 1 544 128 160,
    op 0 320 320 544,
    op 1 544 224 256,
    op 2 320 320 544,
    op 1 352 0 64,
    op 1 544 96 160,
    op 0 352 352 544,
    op 1 544 192 256,
    op 2 352 352 544,
    op 0 544 256 640,
    op 2 480 224 544,
    op 1 512 224 544,
    op 0 384 320 640,
    op 0 448 192 608,
    op 0 416 448 640,
    op 0 544 288 480,
    op 0 384 384 352,
    op 2 384 544 384,
    op 0 544 512 480,
    op 0 416 416 352,
    op 1 416 544 416,
    op 0 544 320 512,
    op 0 448 448 288,
    op 1 448 544 448]

end Libp2pAsm.Asm.Crypto.Weierstrass
