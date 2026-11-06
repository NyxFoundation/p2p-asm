import Libp2pAsm.Asm.Crypto.AES.Circuit
import Libp2pAsm.Spec.Crypto.AES.Basic

/-! Kernel-checked finite cases; split into modules to bound build costs. -/
namespace Libp2pAsm.Refinement.Crypto.AES.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sbox_range_8 (n : Nat) (lo : 128 ≤ n) (hi : n < 144) :
    Asm.Crypto.AES.Circuit.evaluate (BitVec.ofNat 8 n) =
      Spec.Crypto.AES.subByte (BitVec.ofNat 8 n) := by
  have cases : n = 128 ∨ n = 129 ∨ n = 130 ∨ n = 131 ∨ n = 132 ∨ n = 133 ∨ n = 134 ∨ n = 135 ∨ n = 136 ∨ n = 137 ∨ n = 138 ∨ n = 139 ∨ n = 140 ∨ n = 141 ∨ n = 142 ∨ n = 143 := by omega
  rcases cases with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
    <;> subst n <;> decide +kernel

theorem sbox_range_9 (n : Nat) (lo : 144 ≤ n) (hi : n < 160) :
    Asm.Crypto.AES.Circuit.evaluate (BitVec.ofNat 8 n) =
      Spec.Crypto.AES.subByte (BitVec.ofNat 8 n) := by
  have cases : n = 144 ∨ n = 145 ∨ n = 146 ∨ n = 147 ∨ n = 148 ∨ n = 149 ∨ n = 150 ∨ n = 151 ∨ n = 152 ∨ n = 153 ∨ n = 154 ∨ n = 155 ∨ n = 156 ∨ n = 157 ∨ n = 158 ∨ n = 159 := by omega
  rcases cases with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
    <;> subst n <;> decide +kernel

theorem sbox_range_10 (n : Nat) (lo : 160 ≤ n) (hi : n < 176) :
    Asm.Crypto.AES.Circuit.evaluate (BitVec.ofNat 8 n) =
      Spec.Crypto.AES.subByte (BitVec.ofNat 8 n) := by
  have cases : n = 160 ∨ n = 161 ∨ n = 162 ∨ n = 163 ∨ n = 164 ∨ n = 165 ∨ n = 166 ∨ n = 167 ∨ n = 168 ∨ n = 169 ∨ n = 170 ∨ n = 171 ∨ n = 172 ∨ n = 173 ∨ n = 174 ∨ n = 175 := by omega
  rcases cases with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
    <;> subst n <;> decide +kernel

theorem sbox_range_11 (n : Nat) (lo : 176 ≤ n) (hi : n < 192) :
    Asm.Crypto.AES.Circuit.evaluate (BitVec.ofNat 8 n) =
      Spec.Crypto.AES.subByte (BitVec.ofNat 8 n) := by
  have cases : n = 176 ∨ n = 177 ∨ n = 178 ∨ n = 179 ∨ n = 180 ∨ n = 181 ∨ n = 182 ∨ n = 183 ∨ n = 184 ∨ n = 185 ∨ n = 186 ∨ n = 187 ∨ n = 188 ∨ n = 189 ∨ n = 190 ∨ n = 191 := by omega
  rcases cases with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
    <;> subst n <;> decide +kernel

end Libp2pAsm.Refinement.Crypto.AES.Finite
