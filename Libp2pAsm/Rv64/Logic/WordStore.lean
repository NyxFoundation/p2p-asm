import Libp2pAsm.Rv64.Logic.WordMemory

namespace Libp2pAsm.Rv64.Logic

set_option backward.isDefEq.respectTransparency false

def wordByte (value : Word) (i : Nat) : UInt8 := (value >>> (8*i)).toNat.toUInt8

def writeLE64 (bytes : Array UInt8) (offset : Nat) (value : Word) : Array UInt8 :=
  (List.range 8).foldl (fun output i => output.setIfInBounds (offset+i) (wordByte value i)) bytes

@[simp] theorem writeLE64_size (bytes : Array UInt8) (offset : Nat) (value : Word) :
    (writeLE64 bytes offset value).size = bytes.size := by
  simp [writeLE64, List.range_succ]

theorem heap_store_word (base addr value : Word) (bytes : Array UInt8) (frame : List Region)
    (hv : (heap base bytes true frame).valid = true)
    (ha : addr.toNat % 8 = 0) (hb : base.toNat ≤ addr.toNat)
    (hi : addr.toNat - base.toNat + 8 ≤ bytes.size) :
    (heap base bytes true frame).store 8 addr value =
      .ok (heap base (writeLE64 bytes (addr.toNat-base.toNat) value) true frame) := by
  unfold LeanAsm.Rv64.Memory.store
  unfold LeanAsm.Rv64.Memory.locate
  unfold LeanAsm.Rv64.supportedWidth
  simp only [hv]
  have hc : (LeanAsm.Rv64.Region.mk base bytes true).contains 8 addr = true := by
    simp [LeanAsm.Rv64.Region.contains, hb]; omega
  simp [ha, heap, List.findIdx?_toArray, List.findIdx?_cons, hc,
    bind, Except.bind, pure, Except.pure]
  unfold LeanAsm.Rv64.writeBytes
  have h0 : addr.toNat-base.toNat < bytes.size := by omega
  have h1 : addr.toNat-base.toNat+1 < bytes.size := by omega
  have h2 : addr.toNat-base.toNat+2 < bytes.size := by omega
  have h3 : addr.toNat-base.toNat+3 < bytes.size := by omega
  have h4 : addr.toNat-base.toNat+4 < bytes.size := by omega
  have h5 : addr.toNat-base.toNat+5 < bytes.size := by omega
  have h6 : addr.toNat-base.toNat+6 < bytes.size := by omega
  have h7 : addr.toNat-base.toNat+7 < bytes.size := by omega
  simp [writeLE64, wordByte, List.range_succ, h0, h1, h2, h3, h4, h5, h6, h7,
    bind, Except.bind, pure, Except.pure, Array.setIfInBounds]

theorem writeLE64_byte (bytes : Array UInt8) (offset : Nat) (value : Word) (i : Nat)
    (hb : offset+8 ≤ bytes.size) (hi : i < 8) :
    (writeLE64 bytes offset value)[offset+i]?.getD 0 = wordByte value i := by
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [writeLE64, List.range_succ, Array.setIfInBounds,
    show offset < bytes.size by omega, show offset+1 < bytes.size by omega,
    show offset+2 < bytes.size by omega, show offset+3 < bytes.size by omega,
    show offset+4 < bytes.size by omega, show offset+5 < bytes.size by omega,
    show offset+6 < bytes.size by omega, show offset+7 < bytes.size by omega]

theorem writeLE64_frame (bytes : Array UInt8) (offset : Nat) (value : Word) :
    ByteFrame offset 8 bytes (writeLE64 bytes offset value) := by
  have helper (indices : List Nat) (hindices : ∀ i ∈ indices, i < 8)
      (after : Array UInt8) (hf : ByteFrame offset 8 bytes after) :
      ByteFrame offset 8 bytes (indices.foldl
        (fun output i => output.setIfInBounds (offset+i) (wordByte value i)) after) := by
    induction indices generalizing after with
    | nil => exact hf
    | cons i rest ih =>
      apply ih (fun j hj => hindices j (List.mem_cons_of_mem i hj))
      by_cases hb : offset+i < after.size
      · simp only [Array.setIfInBounds, hb, dite_true]
        exact hf.store _ hb (by omega) (by have := hindices i (by simp); omega)
      · simpa [Array.setIfInBounds, hb] using hf
  exact helper (List.range 8) (by simp) bytes (.refl _ _ _)

end Libp2pAsm.Rv64.Logic
