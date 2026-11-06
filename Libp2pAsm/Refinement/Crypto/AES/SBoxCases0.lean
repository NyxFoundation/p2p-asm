import Libp2pAsm.Asm.Crypto.AES.Circuit
import Libp2pAsm.Spec.Crypto.AES.Basic

/-! Kernel-checked finite cases; split into modules to bound build costs. -/
namespace Libp2pAsm.Refinement.Crypto.AES.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sbox_range_0 (n : Nat) (lo : 0 ≤ n) (hi : n < 16) :
    Asm.Crypto.AES.Circuit.evaluate (BitVec.ofNat 8 n) =
      Spec.Crypto.AES.subByte (BitVec.ofNat 8 n) := by
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
  rcases cases with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
    <;> subst n <;> decide +kernel

theorem sbox_range_1 (n : Nat) (lo : 16 ≤ n) (hi : n < 32) :
    Asm.Crypto.AES.Circuit.evaluate (BitVec.ofNat 8 n) =
      Spec.Crypto.AES.subByte (BitVec.ofNat 8 n) := by
  have cases : n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨ n = 30 ∨ n = 31 := by omega
  rcases cases with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
    <;> subst n <;> decide +kernel

theorem sbox_range_2 (n : Nat) (lo : 32 ≤ n) (hi : n < 48) :
    Asm.Crypto.AES.Circuit.evaluate (BitVec.ofNat 8 n) =
      Spec.Crypto.AES.subByte (BitVec.ofNat 8 n) := by
  have cases : n = 32 ∨ n = 33 ∨ n = 34 ∨ n = 35 ∨ n = 36 ∨ n = 37 ∨ n = 38 ∨ n = 39 ∨ n = 40 ∨ n = 41 ∨ n = 42 ∨ n = 43 ∨ n = 44 ∨ n = 45 ∨ n = 46 ∨ n = 47 := by omega
  rcases cases with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
    <;> subst n <;> decide +kernel

theorem sbox_range_3 (n : Nat) (lo : 48 ≤ n) (hi : n < 64) :
    Asm.Crypto.AES.Circuit.evaluate (BitVec.ofNat 8 n) =
      Spec.Crypto.AES.subByte (BitVec.ofNat 8 n) := by
  have cases : n = 48 ∨ n = 49 ∨ n = 50 ∨ n = 51 ∨ n = 52 ∨ n = 53 ∨ n = 54 ∨ n = 55 ∨ n = 56 ∨ n = 57 ∨ n = 58 ∨ n = 59 ∨ n = 60 ∨ n = 61 ∨ n = 62 ∨ n = 63 := by omega
  rcases cases with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
    <;> subst n <;> decide +kernel

end Libp2pAsm.Refinement.Crypto.AES.Finite
