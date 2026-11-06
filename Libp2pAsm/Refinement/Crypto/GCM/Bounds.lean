import Libp2pAsm.Spec.Crypto.GCM.Basic
import Libp2pAsm.Rv64.Basic

namespace Libp2pAsm.Refinement.Crypto.GCM
open Spec.Crypto.GCM

/-- The normative byte limit also enforces the permitted counter-block count. -/
theorem counter_blocks_fit (n : Nat) (h : n ≤ maxMessageBytes) :
    (n + 15) / 16 ≤ 2^32 - 2 := by
  unfold maxMessageBytes at h
  omega

/-- Counter 1 masks the tag; data counters start at 2 and end at most ffffffff. -/
theorem last_counter_fits (n i : Nat) (h : n ≤ maxMessageBytes)
    (hi : i < (n+15)/16) : i+2 < 2^32 := by
  have := counter_blocks_fit n h
  omega

theorem aad_bits_fit (n : Nat) (h : n ≤ maxAadBytes) : n*8 < 2^64 := by
  unfold maxAadBytes at h
  omega

theorem message_bits_fit (n : Nat) (h : n ≤ maxMessageBytes) : n*8 < 2^64 := by
  unfold maxMessageBytes at h
  omega

theorem seal_length_fits (n : Nat) (h : n ≤ maxMessageBytes) : n+16 < 2^64 := by
  unfold maxMessageBytes at h
  omega

/-- Exact branchless commit expression, independently of AES or pointer state. -/
def commit (plain old mask : Rv64.Word) : Rv64.Word :=
  (plain &&& mask) ||| (old &&& ~~~mask)

theorem failed_commit_unchanged (plain old : Rv64.Word) : commit plain old 0 = old := by
  ext i h
  simp only [commit, BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
  simp

theorem successful_commit (plain old : Rv64.Word) : commit plain old (-1) = plain := by
  have all : (-1 : Rv64.Word) = BitVec.allOnes 64 := by decide
  rw [all]
  ext i h
  simp only [commit, BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_allOnes]
  simp

/-- The SLTU-derived mismatch bit is converted to a mask without a branch. -/
theorem tag_mask (difference : Rv64.Word) :
    ((if (0 : Rv64.Word) < difference then 1 else 0) - 1 : Rv64.Word) =
      (if difference = 0 then -1 else 0) := by
  change ((if (0 : BitVec 64) < difference then 1 else 0) - 1 : BitVec 64) =
    (if difference = (0 : BitVec 64) then -1 else 0)
  split <;> split <;> simp_all

/-- Conservative proposed fuel budget for valid calls, expressed in public
lengths. Tests check the budget; a universal fetch/memory/termination proof is
still required before using this as a proved resource contract. -/
def fuelBudget (messageLength aadLength : Nat) : Nat :=
  100000 + 40000 * ((messageLength+15)/16 + (aadLength+15)/16)

end Libp2pAsm.Refinement.Crypto.GCM
