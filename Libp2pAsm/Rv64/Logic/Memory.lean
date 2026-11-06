import Libp2pAsm.Rv64.Memory
import Libp2pAsm.Rv64.Logic.Unfold

set_option backward.isDefEq.respectTransparency false

namespace Libp2pAsm.Rv64.Logic

/-- An owned byte array and an arbitrary disjoint frame of other regions. -/
def heap (base : Word) (bytes : Array UInt8) (writable : Bool) (frame : List Region) : Memory :=
  ⟨(⟨base, bytes, writable⟩ :: frame).toArray⟩

theorem heap_valid_congr (base : Word) (a b : Array UInt8) (w : Bool) (frame : List Region)
    (h : a.size = b.size) : (heap base a w frame).valid = (heap base b w frame).valid := by
  simp [heap, Memory.valid, Region.valid, Region.disjoint, Region.endAddr, h,
    List.pairwise_cons, Bool.decide_and]

theorem heap_load_byte (base addr : Word) (bytes : Array UInt8) (w : Bool) (frame : List Region)
    (hv : (heap base bytes w frame).valid = true)
    (hb : base.toNat ≤ addr.toNat) (hi : addr.toNat - base.toNat < bytes.size) :
    (heap base bytes w frame).load 1 addr =
      .ok (BitVec.ofNat 64 bytes[addr.toNat - base.toNat].toNat) := by
  unfold Memory.load
  unfold_internal Libp2pAsm.Rv64.Memory.locate
  unfold_internal Libp2pAsm.Rv64.supportedWidth
  simp only [hv]
  have hc : (Region.mk base bytes w).contains 1 addr = true := by
    simp [Region.contains, hb]; omega
  simp [Nat.mod_one, heap, List.findIdx?_toArray, List.findIdx?_cons, hc,
    bind, Except.bind, pure, Except.pure]
  unfold_internal Libp2pAsm.Rv64.readBytes
  simp [List.range_succ, hi, bind, Except.bind, pure, Except.pure]

theorem heap_store_byte (base addr value : Word) (bytes : Array UInt8) (frame : List Region)
    (hv : (heap base bytes true frame).valid = true)
    (hb : base.toNat ≤ addr.toNat) (hi : addr.toNat - base.toNat < bytes.size) :
    (heap base bytes true frame).store 1 addr value =
      .ok (heap base (bytes.set (addr.toNat - base.toNat) value.toNat.toUInt8) true frame) := by
  unfold Memory.store
  unfold_internal Libp2pAsm.Rv64.Memory.locate
  unfold_internal Libp2pAsm.Rv64.supportedWidth
  simp only [hv]
  have hc : (Region.mk base bytes true).contains 1 addr = true := by
    simp [Region.contains, hb]; omega
  simp [Nat.mod_one, heap, List.findIdx?_toArray, List.findIdx?_cons, hc,
    bind, Except.bind, pure, Except.pure]
  unfold_internal Libp2pAsm.Rv64.writeBytes
  simp [List.range_succ, hi, bind, Except.bind, pure, Except.pure]

/-- Byte stores keep the permissions, addresses, lengths, and all other regions. -/
theorem heap_store_valid (base : Word) (bytes : Array UInt8) (frame : List Region)
    (i : Nat) (v : UInt8) (hi : i < bytes.size)
    (hv : (heap base bytes true frame).valid = true) :
    (heap base (bytes.set i v) true frame).valid = true := by
  rw [← heap_valid_congr base bytes (bytes.set i v) true frame (by simp)]
  exact hv

/-- An array frame states equality of every byte outside the owned interval. -/
def ByteFrame (lo count : Nat) (before after : Array UInt8) : Prop :=
  before.size = after.size ∧ ∀ i (hb : i < before.size) (ha : i < after.size),
    (i < lo ∨ lo + count ≤ i) → after[i] = before[i]

theorem ByteFrame.refl (lo count : Nat) (bytes : Array UInt8) :
    ByteFrame lo count bytes bytes := ⟨rfl, fun _ _ _ _ => rfl⟩

theorem ByteFrame.store {lo count i : Nat} {before after : Array UInt8} (v : UInt8)
    (h : ByteFrame lo count before after) (hi : i < after.size)
    (hl : lo ≤ i) (hu : i < lo + count) :
    ByteFrame lo count before (after.set i v) := by
  refine ⟨by simpa using h.1, ?_⟩
  intro j hb ha hj
  have hji : j ≠ i := by omega
  simp only [Array.getElem_set_ne hi (by simpa using ha) (Ne.symm hji)]
  exact h.2 j hb (by simpa using ha) hj

end Libp2pAsm.Rv64.Logic
