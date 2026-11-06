import Libp2pAsm.Asm.Crypto.Weierstrass.Field

/-! HACL* complete homogeneous projective formula, translated to canonical
Montgomery field calls. Copyright INRIA, CMU, Microsoft and HACL* contributors.
MIT: LICENSES/hacl-weierstrass.txt. See README for immutable provenance.
This port does not inherit the upstream verification proof. -/
namespace Libp2pAsm.Asm.Crypto.Weierstrass
open Link

def formulaP256 : Part := .seq [
    op 0 192 0 96,
    op 0 224 32 128,
    op 0 256 64 160,
    op 1 288 0 32,
    op 1 320 96 128,
    op 0 288 288 320,
    op 1 320 192 224,
    op 2 288 288 320,
    op 1 320 32 64,
    op 1 352 128 160,
    op 0 320 320 352,
    op 1 352 224 256,
    op 2 320 320 352,
    op 1 384 0 64,
    op 1 416 96 160,
    op 0 384 384 416,
    op 1 416 192 256,
    op 2 416 384 416,
    op 0 448 256 576,
    op 2 384 416 448,
    op 1 448 384 384,
    op 1 384 384 448,
    op 2 448 224 384,
    op 1 384 224 384,
    op 0 416 416 576,
    op 1 224 256 256,
    op 1 256 224 256,
    op 2 416 416 256,
    op 2 416 416 192,
    op 1 224 416 416,
    op 1 416 224 416,
    op 1 224 192 192,
    op 1 192 224 192,
    op 2 192 192 256,
    op 0 224 320 416,
    op 0 256 192 416,
    op 0 416 384 448,
    op 1 416 416 256,
    op 0 384 288 384,
    op 2 384 384 224,
    op 0 448 320 448,
    op 0 224 288 192,
    op 1 448 448 224]

end Libp2pAsm.Asm.Crypto.Weierstrass
