import Libp2pAsm.Refinement.Crypto.AES.SBoxCases0
import Libp2pAsm.Refinement.Crypto.AES.SBoxCases1
import Libp2pAsm.Refinement.Crypto.AES.SBoxCases2
import Libp2pAsm.Refinement.Crypto.AES.SBoxCases3

namespace Libp2pAsm.Refinement.Crypto.AES
open Finite

/-- Exhaustive finite-domain equality checked by Lean's kernel. This relates
our Boolean circuit to independent GF(2^8) inversion and affine transform;
it is not a proof of memory/fetch execution or multi-lane transposition. -/
theorem sbox_all_bytes (b : Fin 256) :
    Asm.Crypto.AES.Circuit.evaluate (BitVec.ofNat 8 b.val) =
      Spec.Crypto.AES.subByte (BitVec.ofNat 8 b.val) := by
  by_cases h0 : b.val < 16
  · exact sbox_range_0 b.val (by omega) h0
  by_cases h1 : b.val < 32
  · exact sbox_range_1 b.val (by omega) h1
  by_cases h2 : b.val < 48
  · exact sbox_range_2 b.val (by omega) h2
  by_cases h3 : b.val < 64
  · exact sbox_range_3 b.val (by omega) h3
  by_cases h4 : b.val < 80
  · exact sbox_range_4 b.val (by omega) h4
  by_cases h5 : b.val < 96
  · exact sbox_range_5 b.val (by omega) h5
  by_cases h6 : b.val < 112
  · exact sbox_range_6 b.val (by omega) h6
  by_cases h7 : b.val < 128
  · exact sbox_range_7 b.val (by omega) h7
  by_cases h8 : b.val < 144
  · exact sbox_range_8 b.val (by omega) h8
  by_cases h9 : b.val < 160
  · exact sbox_range_9 b.val (by omega) h9
  by_cases h10 : b.val < 176
  · exact sbox_range_10 b.val (by omega) h10
  by_cases h11 : b.val < 192
  · exact sbox_range_11 b.val (by omega) h11
  by_cases h12 : b.val < 208
  · exact sbox_range_12 b.val (by omega) h12
  by_cases h13 : b.val < 224
  · exact sbox_range_13 b.val (by omega) h13
  by_cases h14 : b.val < 240
  · exact sbox_range_14 b.val (by omega) h14
  exact sbox_range_15 b.val (by omega) b.isLt

/-- All gate sources are initialized and all static offsets fit signed imm12. -/
theorem circuit_static_bounds :
    (Asm.Crypto.AES.Circuit.gates.zipIdx.all fun (g, i) =>
      g.dst == i+8 && g.left < g.dst && g.right < g.dst && 8*g.dst < 2048) = true := by decide +kernel

end Libp2pAsm.Refinement.Crypto.AES
