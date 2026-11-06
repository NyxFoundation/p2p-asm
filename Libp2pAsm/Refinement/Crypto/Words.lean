import Libp2pAsm.Asm.Crypto.Sha2
import Libp2pAsm.Spec.Crypto.SHA256
import Libp2pAsm.Spec.Crypto.SHA512

/-!
Universal word identities for the expressions emitted by Asm.Crypto.Sha2.
Proofs use ordinary BitVec lemmas and kernel reduction. These are identities, not
whole-function, instruction-fetch, memory safety or constant-time proofs.
-/

namespace Libp2pAsm.Refinement.Crypto

open Rv64

def low32 (x : Word) : Word := x &&& 0xffffffff

def rotate32 (x : Word) (n : Nat) : Word :=
  low32 ((x >>> n) ||| (x <<< (32 - n)))

def rotate64 (x : Word) (n : Nat) : Word :=
  (x >>> n) ||| (x <<< (64 - n))

theorem low32_eq (x : Word) : low32 x = (x.setWidth 32).zeroExtend 64 := by
  have mask : (0xffffffff : Word) = ((BitVec.allOnes 32).zeroExtend 64) := by decide
  unfold low32
  rw [mask]
  ext i h
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.getElem_and, BitVec.getElem_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, BitVec.getLsbD_eq_getElem h]
  exact Bool.and_comm _ _

theorem add32_eq (x y : Word) :
    low32 (x + y) = ((x.setWidth 32) + (y.setWidth 32)).zeroExtend 64 := by
  rw [low32_eq, BitVec.setWidth_add x y (by decide)]

theorem choose_eq (x y z : Word) :
    z ^^^ (x &&& (y ^^^ z)) = Spec.Crypto.Sha2.choose x y z := by
  ext i h
  simp only [Spec.Crypto.Sha2.choose, BitVec.getElem_xor, BitVec.getElem_and,
    BitVec.getElem_not]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> decide

theorem majority_eq (x y z : Word) :
    (x &&& y) ||| ((x ||| y) &&& z) = Spec.Crypto.Sha2.majority x y z := by
  ext i h
  simp only [Spec.Crypto.Sha2.majority, BitVec.getElem_xor, BitVec.getElem_and,
    BitVec.getElem_or]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> decide

theorem rotate32_eq (x : BitVec 32) (n : Nat) (h : n < 32) :
    rotate32 (x.zeroExtend 64) n = (x.rotateRight n).zeroExtend 64 := by
  unfold rotate32
  rw [low32_eq]
  simp only [BitVec.zeroExtend_eq_setWidth]
  rw [← BitVec.setWidth_ushiftRight (by decide : 32 ≤ 64)]
  simp only [BitVec.setWidth_or, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
    BitVec.setWidth_shiftLeft_of_le (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt h, BitVec.setWidth_or]

theorem rotate64_eq (x : Word) (n : Nat) (h : n < 64) :
    rotate64 x n = x.rotateRight n := by
  simp [rotate64, BitVec.rotateRight_def, Nat.mod_eq_of_lt h]

theorem bigSigma0_32_eq (x : BitVec 32) :
    rotate32 (x.zeroExtend 64) 2 ^^^ rotate32 (x.zeroExtend 64) 13 ^^^
      rotate32 (x.zeroExtend 64) 22 = (Spec.Crypto.SHA256.bigSigma0 x).zeroExtend 64 := by
  rw [rotate32_eq x 2 (by decide), rotate32_eq x 13 (by decide), rotate32_eq x 22 (by decide)]
  simp [Spec.Crypto.SHA256.bigSigma0]

theorem bigSigma1_32_eq (x : BitVec 32) :
    rotate32 (x.zeroExtend 64) 6 ^^^ rotate32 (x.zeroExtend 64) 11 ^^^
      rotate32 (x.zeroExtend 64) 25 = (Spec.Crypto.SHA256.bigSigma1 x).zeroExtend 64 := by
  rw [rotate32_eq x 6 (by decide), rotate32_eq x 11 (by decide), rotate32_eq x 25 (by decide)]
  simp [Spec.Crypto.SHA256.bigSigma1]

theorem smallSigma0_32_eq (x : BitVec 32) :
    rotate32 (x.zeroExtend 64) 7 ^^^ rotate32 (x.zeroExtend 64) 18 ^^^
      ((x.zeroExtend 64) >>> 3) = (Spec.Crypto.SHA256.smallSigma0 x).zeroExtend 64 := by
  rw [rotate32_eq x 7 (by decide), rotate32_eq x 18 (by decide)]
  simp [Spec.Crypto.SHA256.smallSigma0, BitVec.setWidth_ushiftRight (by decide : 32 ≤ 64)]

theorem smallSigma1_32_eq (x : BitVec 32) :
    rotate32 (x.zeroExtend 64) 17 ^^^ rotate32 (x.zeroExtend 64) 19 ^^^
      ((x.zeroExtend 64) >>> 10) = (Spec.Crypto.SHA256.smallSigma1 x).zeroExtend 64 := by
  rw [rotate32_eq x 17 (by decide), rotate32_eq x 19 (by decide)]
  simp [Spec.Crypto.SHA256.smallSigma1, BitVec.setWidth_ushiftRight (by decide : 32 ≤ 64)]

theorem bigSigma0_64_eq (x : Word) :
    rotate64 x 28 ^^^ rotate64 x 34 ^^^ rotate64 x 39 = Spec.Crypto.SHA512.bigSigma0 x := by
  simp [rotate64_eq, Spec.Crypto.SHA512.bigSigma0]

theorem bigSigma1_64_eq (x : Word) :
    rotate64 x 14 ^^^ rotate64 x 18 ^^^ rotate64 x 41 = Spec.Crypto.SHA512.bigSigma1 x := by
  simp [rotate64_eq, Spec.Crypto.SHA512.bigSigma1]

theorem smallSigma0_64_eq (x : Word) :
    rotate64 x 1 ^^^ rotate64 x 8 ^^^ (x >>> 7) = Spec.Crypto.SHA512.smallSigma0 x := by
  simp [rotate64_eq, Spec.Crypto.SHA512.smallSigma0]

theorem smallSigma1_64_eq (x : Word) :
    rotate64 x 19 ^^^ rotate64 x 61 ^^^ (x >>> 6) = Spec.Crypto.SHA512.smallSigma1 x := by
  simp [rotate64_eq, Spec.Crypto.SHA512.smallSigma1]

end Libp2pAsm.Refinement.Crypto
