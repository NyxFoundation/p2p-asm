import Libp2pAsm.Asm.Crypto.AES.Circuit
import Libp2pAsm.Spec.Crypto.AES.Basic

/-! Kernel-checked finite cases; split into modules to bound build costs. -/
namespace Libp2pAsm.Refinement.Crypto.AES.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sbox_range_4 (n : Nat) (lo : 64 ≤ n) (hi : n < 80) :
    Asm.Crypto.AES.Circuit.evaluate (BitVec.ofNat 8 n) =
      Spec.Crypto.AES.subByte (BitVec.ofNat 8 n) := by
  have cases : n = 64 ∨ n = 65 ∨ n = 66 ∨ n = 67 ∨ n = 68 ∨ n = 69 ∨ n = 70 ∨ n = 71 ∨ n = 72 ∨ n = 73 ∨ n = 74 ∨ n = 75 ∨ n = 76 ∨ n = 77 ∨ n = 78 ∨ n = 79 := by omega
  rcases cases with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
    <;> subst n <;> decide +kernel

theorem sbox_range_5 (n : Nat) (lo : 80 ≤ n) (hi : n < 96) :
    Asm.Crypto.AES.Circuit.evaluate (BitVec.ofNat 8 n) =
      Spec.Crypto.AES.subByte (BitVec.ofNat 8 n) := by
  have cases : n = 80 ∨ n = 81 ∨ n = 82 ∨ n = 83 ∨ n = 84 ∨ n = 85 ∨ n = 86 ∨ n = 87 ∨ n = 88 ∨ n = 89 ∨ n = 90 ∨ n = 91 ∨ n = 92 ∨ n = 93 ∨ n = 94 ∨ n = 95 := by omega
  rcases cases with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
    <;> subst n <;> decide +kernel

theorem sbox_range_6 (n : Nat) (lo : 96 ≤ n) (hi : n < 112) :
    Asm.Crypto.AES.Circuit.evaluate (BitVec.ofNat 8 n) =
      Spec.Crypto.AES.subByte (BitVec.ofNat 8 n) := by
  have cases : n = 96 ∨ n = 97 ∨ n = 98 ∨ n = 99 ∨ n = 100 ∨ n = 101 ∨ n = 102 ∨ n = 103 ∨ n = 104 ∨ n = 105 ∨ n = 106 ∨ n = 107 ∨ n = 108 ∨ n = 109 ∨ n = 110 ∨ n = 111 := by omega
  rcases cases with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
    <;> subst n <;> decide +kernel

theorem sbox_range_7 (n : Nat) (lo : 112 ≤ n) (hi : n < 128) :
    Asm.Crypto.AES.Circuit.evaluate (BitVec.ofNat 8 n) =
      Spec.Crypto.AES.subByte (BitVec.ofNat 8 n) := by
  have cases : n = 112 ∨ n = 113 ∨ n = 114 ∨ n = 115 ∨ n = 116 ∨ n = 117 ∨ n = 118 ∨ n = 119 ∨ n = 120 ∨ n = 121 ∨ n = 122 ∨ n = 123 ∨ n = 124 ∨ n = 125 ∨ n = 126 ∨ n = 127 := by omega
  rcases cases with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
    <;> subst n <;> decide +kernel

end Libp2pAsm.Refinement.Crypto.AES.Finite
