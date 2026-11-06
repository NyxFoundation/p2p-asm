import Libp2pAsm.Asm.Crypto.AES.Circuit
import Libp2pAsm.Spec.Crypto.AES.Basic

/-! Kernel-checked finite cases; split into modules to bound build costs. -/
namespace Libp2pAsm.Refinement.Crypto.AES.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sbox_range_12 (n : Nat) (lo : 192 ≤ n) (hi : n < 208) :
    Asm.Crypto.AES.Circuit.evaluate (BitVec.ofNat 8 n) =
      Spec.Crypto.AES.subByte (BitVec.ofNat 8 n) := by
  have cases : n = 192 ∨ n = 193 ∨ n = 194 ∨ n = 195 ∨ n = 196 ∨ n = 197 ∨ n = 198 ∨ n = 199 ∨ n = 200 ∨ n = 201 ∨ n = 202 ∨ n = 203 ∨ n = 204 ∨ n = 205 ∨ n = 206 ∨ n = 207 := by omega
  rcases cases with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
    <;> subst n <;> decide +kernel

theorem sbox_range_13 (n : Nat) (lo : 208 ≤ n) (hi : n < 224) :
    Asm.Crypto.AES.Circuit.evaluate (BitVec.ofNat 8 n) =
      Spec.Crypto.AES.subByte (BitVec.ofNat 8 n) := by
  have cases : n = 208 ∨ n = 209 ∨ n = 210 ∨ n = 211 ∨ n = 212 ∨ n = 213 ∨ n = 214 ∨ n = 215 ∨ n = 216 ∨ n = 217 ∨ n = 218 ∨ n = 219 ∨ n = 220 ∨ n = 221 ∨ n = 222 ∨ n = 223 := by omega
  rcases cases with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
    <;> subst n <;> decide +kernel

theorem sbox_range_14 (n : Nat) (lo : 224 ≤ n) (hi : n < 240) :
    Asm.Crypto.AES.Circuit.evaluate (BitVec.ofNat 8 n) =
      Spec.Crypto.AES.subByte (BitVec.ofNat 8 n) := by
  have cases : n = 224 ∨ n = 225 ∨ n = 226 ∨ n = 227 ∨ n = 228 ∨ n = 229 ∨ n = 230 ∨ n = 231 ∨ n = 232 ∨ n = 233 ∨ n = 234 ∨ n = 235 ∨ n = 236 ∨ n = 237 ∨ n = 238 ∨ n = 239 := by omega
  rcases cases with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
    <;> subst n <;> decide +kernel

theorem sbox_range_15 (n : Nat) (lo : 240 ≤ n) (hi : n < 256) :
    Asm.Crypto.AES.Circuit.evaluate (BitVec.ofNat 8 n) =
      Spec.Crypto.AES.subByte (BitVec.ofNat 8 n) := by
  have cases : n = 240 ∨ n = 241 ∨ n = 242 ∨ n = 243 ∨ n = 244 ∨ n = 245 ∨ n = 246 ∨ n = 247 ∨ n = 248 ∨ n = 249 ∨ n = 250 ∨ n = 251 ∨ n = 252 ∨ n = 253 ∨ n = 254 ∨ n = 255 := by omega
  rcases cases with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
    <;> subst n <;> decide +kernel

end Libp2pAsm.Refinement.Crypto.AES.Finite
