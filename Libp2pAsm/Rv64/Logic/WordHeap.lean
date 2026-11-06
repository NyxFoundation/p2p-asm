import Libp2pAsm.Rv64.Logic.WordRoundtrip

namespace Libp2pAsm.Rv64.Logic

theorem heap_bounded {base : Word} {bytes : Array UInt8} {w : Bool} {frame : List Region}
    (hv : (heap base bytes w frame).valid = true) : base.toNat+bytes.size ≤ 2^64 := by
  simp only [heap, Memory.valid, Bool.and_eq_true, Array.all_eq_true] at hv
  have hh := hv.1 0 (by simp)
  change decide (0 < bytes.size ∧ base.toNat+bytes.size ≤ 2^64) = true at hh
  exact (of_decide_eq_true hh).2

theorem word_offset_toNat {base : Word} {bytes : Array UInt8} {w : Bool} {frame : List Region}
    (hv : (heap base bytes w frame).valid = true) (offset : Nat) (ho : offset < bytes.size) :
    (base+BitVec.ofNat 64 offset).toNat = base.toNat+offset := by
  have hb := heap_bounded hv
  have hn : offset < 2^64 := by omega
  have ha : base.toNat+offset < 2^64 := by omega
  simp [BitVec.toNat_add, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt ha]

theorem heap_wordAt (base : Word) (bytes : Array UInt8) (w : Bool) (frame : List Region)
    (hv : (heap base bytes w frame).valid = true) (ha : base.toNat%8 = 0)
    (offset : Nat) (ho : offset%8 = 0) (hf : offset+8 ≤ bytes.size) :
    WordAt (heap base bytes w frame) (base+BitVec.ofNat 64 offset) (readLE64 bytes offset) := by
  have hn := word_offset_toNat hv offset (by omega)
  refine ⟨0, { present := by simp [heap], aligned := ?_, lower := ?_, fits := ?_, bytes := ?_ }⟩
  · simp [hn, Nat.add_mod, ha, ho]
  · change base.toNat ≤ (base+BitVec.ofNat 64 offset).toNat
    rw [hn]; omega
  · change (base+BitVec.ofNat 64 offset).toNat-base.toNat+8 ≤ bytes.size
    simpa [hn] using hf
  · change readLE64 bytes offset = readLE64 bytes ((base+BitVec.ofNat 64 offset).toNat-base.toNat)
    simp [hn]

theorem heap_store_word_offset (base value : Word) (bytes : Array UInt8) (frame : List Region)
    (hv : (heap base bytes true frame).valid = true) (ha : base.toNat%8 = 0)
    (offset : Nat) (ho : offset%8 = 0) (hf : offset+8 ≤ bytes.size) :
    (heap base bytes true frame).store 8 (base+BitVec.ofNat 64 offset) value =
      .ok (heap base (writeLE64 bytes offset value) true frame) := by
  have hn := word_offset_toNat hv offset (by omega)
  simpa [hn] using heap_store_word base (base+BitVec.ofNat 64 offset) value bytes frame hv
    (by simp [hn, Nat.add_mod, ha, ho]) (by omega) (by simp [hn]; exact hf)

theorem readLE64_frame {before after : Array UInt8} {lo count offset : Nat}
    (h : ByteFrame lo count before after) (hb : offset+8 ≤ before.size)
    (hd : offset+8 ≤ lo ∨ lo+count ≤ offset) :
    readLE64 after offset = readLE64 before offset := by
  have he (i : Nat) (hi : i < 8) : after[offset+i]?.getD 0 = before[offset+i]?.getD 0 := by
    have hb' : offset+i < before.size := by omega
    have ha' : offset+i < after.size := by have := h.1; omega
    simpa [hb', ha'] using h.2 (offset+i) hb' ha' (by omega)
  simp only [readLE64, List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [he 0 (by decide), he 1 (by decide), he 2 (by decide), he 3 (by decide),
    he 4 (by decide), he 5 (by decide), he 6 (by decide), he 7 (by decide)]

end Libp2pAsm.Rv64.Logic
