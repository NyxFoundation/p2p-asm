import Libp2pAsm.Spec.Crypto.RSA.EMSA
import Libp2pAsm.Asm.Crypto.RSA.Abi

namespace Libp2pAsm.Refinement.Crypto.RSA
open Spec.Crypto.RSA

theorem i2osp_length (width n : Nat) : (i2osp width n).length = width := by
  simp [i2osp]

theorem os2ip_bound (bs : List UInt8) : os2ip bs < 256^bs.length := by
  induction bs with
  | nil => simp [os2ip]
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.toBitVec.isLt
    have hp : 0 < 256^bs.length := Nat.pow_pos (by decide)
    have hm := Nat.mul_le_mul_right (256^bs.length) (show b.toNat ≤ 255 by omega)
    simp only [os2ip, List.length_cons, Nat.pow_succ]
    omega

theorem os2ip_append (xs ys : List UInt8) :
    os2ip (xs ++ ys) = os2ip xs * 256^ys.length + os2ip ys := by
  induction xs with
  | nil => simp [os2ip]
  | cons b bs ih => simp [os2ip, ih, Nat.pow_add,
      Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

theorem os2ip_single (b : UInt8) : os2ip [b] = b.toNat := by simp [os2ip]

theorem key_domain (nb eb : List UInt8) (h : validKey nb eb = true) :
    5 ≤ os2ip nb ∧ os2ip nb % 2 = 1 ∧ 3 ≤ os2ip eb ∧
      os2ip eb % 2 = 1 ∧ os2ip eb < os2ip nb := by
  simp [validKey] at h
  omega

theorem rsavp1_rejects_oversize (nb eb sig : List UInt8)
    (h : os2ip nb ≤ os2ip sig) : rsavp1 nb eb sig = none := by
  simp [rsavp1, show ¬os2ip sig < os2ip nb by omega]

theorem pkcs_encoding_length (k : Nat) (digest em : List UInt8)
    (h : pkcsEncode k digest = some em) : em.length = k := by
  unfold pkcsEncode at h
  split at h
  next accepted =>
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at accepted
    simp [digestInfo, accepted.1]
    omega
  next => contradiction

theorem pkcs_padding_minimum (k : Nat) (digest em : List UInt8)
    (h : pkcsEncode k digest = some em) : 8 ≤ k-54 := by
  unfold pkcsEncode at h
  split at h
  next accepted => simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at accepted; omega
  next => contradiction

theorem pkcs_exact_encoding (digest em : List UInt8) (h : pkcsVerify digest em = true) :
    em = [0,1] ++ List.replicate (em.length-54) 0xff ++ [0] ++ digestInfo ++ digest := by
  simp only [pkcsVerify, beq_iff_eq] at h
  unfold pkcsEncode at h
  split at h
  next => exact (Option.some.inj h).symm
  next => contradiction

theorem pss_emlen_cases (bits : Nat) (h : 1 ≤ bits) :
    (bits+7)/8 = (bits-1+7)/8 ∨ (bits+7)/8 = (bits-1+7)/8+1 := by omega

theorem pss_short_em (bits : Nat) (h : bits%8 = 1) :
    (bits+7)/8 = (bits-1+7)/8+1 := by omega

theorem pss_unused_bits (bits : Nat) (_h : 0 < bits) :
    8*((bits+7)/8)-bits < 8 := by omega

theorem slot_capacity (k : Nat) : k ≤ 4*Asm.Crypto.RSA.limbs k := by
  simp only [Asm.Crypto.RSA.limbs]
  omega

theorem workspace_exact (k : Nat) : Asm.Crypto.RSA.workspaceBytes k =
    8*(Asm.Crypto.RSA.limbs k*7)+896 := by
  simp only [Asm.Crypto.RSA.workspaceBytes]
  omega

theorem workspace_aligned (k : Nat) : Asm.Crypto.RSA.workspaceBytes k % 8 = 0 := by
  simp only [Asm.Crypto.RSA.workspaceBytes]
  omega

theorem estimator_fits (k e : Nat) (hk : k ≤ 65536) (he : e ≤ 65536) :
    Asm.Crypto.RSA.workBound k e < 2^64 := by
  have hl : Asm.Crypto.RSA.limbs k ≤ 16384 := by
    simp only [Asm.Crypto.RSA.limbs]; omega
  have hsq := Nat.mul_le_mul hl hl
  have hs := Nat.mul_le_mul (show Asm.Crypto.RSA.limbs k+1 ≤ 16385 by omega)
    (show Asm.Crypto.RSA.limbs k+1 ≤ 16385 by omega)
  have hp := Nat.mul_le_mul (Nat.mul_le_mul_left 64 hs)
    (show 16*e+4 ≤ 1048580 by omega)
  unfold Asm.Crypto.RSA.workBound
  simp only [Nat.pow_two, Nat.mul_assoc 4096]
  omega

end Libp2pAsm.Refinement.Crypto.RSA
