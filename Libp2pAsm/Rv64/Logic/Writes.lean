import Libp2pAsm.Rv64.Logic.Bytes

namespace Libp2pAsm.Rv64.Logic

set_option backward.isDefEq.respectTransparency false

/-- In-order byte replacement; out-of-range indices are never used by the contracts below. -/
def patchBytes (before : Array UInt8) (offset : Nat) : List UInt8 → Array UInt8
  | [] => before
  | b :: bs => patchBytes (before.setIfInBounds offset b) (offset+1) bs

@[simp] theorem patchBytes_size (before : Array UInt8) (offset : Nat) (bytes : List UInt8) :
    (patchBytes before offset bytes).size = before.size := by
  induction bytes generalizing before offset <;> simp [patchBytes, *]

theorem patchBytes_frame (before : Array UInt8) (offset : Nat) (bytes : List UInt8) :
    ByteFrame offset bytes.length before (patchBytes before offset bytes) := by
  induction bytes generalizing before offset with
  | nil => exact .refl _ _ _
  | cons b bs ih =>
    refine ⟨by simp, ?_⟩
    intro i hi hj hout
    have htail : i < offset + 1 ∨ offset + 1 + bs.length ≤ i := by simp_all; omega
    have he := (ih (before.setIfInBounds offset b) (offset+1)).2 i
      (by simpa using hi) (by simpa using hj) htail
    have hne : offset ≠ i := by simp only [List.length_cons] at hout; omega
    rw [Array.getElem_setIfInBounds_ne hi hne] at he
    exact he

theorem patchBytes_get (before : Array UInt8) (offset : Nat) (bytes : List UInt8)
    (hb : offset + bytes.length ≤ before.size) (j : Nat) (hj : j < bytes.length) :
    (patchBytes before offset bytes)[offset+j]'(by simp; omega) = bytes[j] := by
  induction bytes generalizing before offset j with
  | nil => simp at hj
  | cons b bs ih =>
    cases j with
    | zero =>
      have hf := patchBytes_frame (before.setIfInBounds offset b) (offset+1) bs
      have ho : offset < before.size := by simp only [List.length_cons] at hb; omega
      have he := hf.2 offset (by simpa using ho) (by simpa using ho) (Or.inl (by omega))
      simpa [patchBytes, Array.getElem_setIfInBounds, ho] using he
    | succ j =>
      have he := ih (before.setIfInBounds offset b) (offset+1) (by simp_all; omega) j (by simpa using hj)
      simpa [patchBytes, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

theorem heap_store_at (base value : Word) (before : Array UInt8) (frame : List Region) (i : Nat)
    (hv : (heap base before true frame).valid = true)
    (hb : base.toNat + before.size ≤ 2^64) (hi : i < before.size) :
    (heap base before true frame).store 1 (base + BitVec.ofNat 64 i) value =
      .ok (heap base (before.setIfInBounds i value.toNat.toUInt8) true frame) := by
  have hi64 : i < 2^64 := by omega
  have ha : (base + BitVec.ofNat 64 i).toNat = base.toNat + i := by
    simp [BitVec.toNat_add, Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt (show base.toNat + i < 2^64 by omega)]
  have he := heap_store_byte base (base + BitVec.ofNat 64 i) value before frame hv
    (by omega) (by simpa [ha] using hi)
  simpa [ha, Array.setIfInBounds, hi] using he

end Libp2pAsm.Rv64.Logic
