import Libp2pAsm.Rv64.Logic.Memory

set_option backward.isDefEq.respectTransparency false

namespace Libp2pAsm.Rv64.Logic

/-- A read slice for modular loop contracts; `heap_reads` derives it from actual ownership. -/
def Reads (m : Memory) (ptr : Word) (bytes : List UInt8) : Prop :=
  ∀ i (hi : i < bytes.length), m.load 1 (ptr + BitVec.ofNat 64 i) =
    .ok (BitVec.ofNat 64 bytes[i].toNat)

theorem Reads.head {m ptr b bs} (h : Reads m ptr (b :: bs)) :
    m.load 1 ptr = .ok (BitVec.ofNat 64 b.toNat) := by
  have he := h 0 (by simp)
  change m.load 1 (ptr + 0) = .ok (BitVec.ofNat 64 b.toNat) at he
  simpa using he

theorem Reads.tail {m ptr b bs} (h : Reads m ptr (b :: bs)) : Reads m (ptr + 1) bs := by
  intro i hi
  have he := h (i + 1) (by simpa using hi)
  have hp : ptr + 1 + BitVec.ofNat 64 i = ptr + BitVec.ofNat 64 (i + 1) := by
    rw [BitVec.ofNat_add]
    rw [BitVec.add_assoc, BitVec.add_comm (1 : Word) (BitVec.ofNat 64 i)]
    rfl
  rw [hp]
  exact he

theorem heap_reads (base : Word) (bytes : List UInt8) (w : Bool) (frame : List Region)
    (hv : (heap base bytes.toArray w frame).valid = true)
    (hb : base.toNat + bytes.length ≤ 2^64) :
    Reads (heap base bytes.toArray w frame) base bytes := by
  intro i hi
  have hsum : base.toNat + i < 2^64 := by omega
  have hi64 : i < 2^64 := by omega
  have ha : (base + BitVec.ofNat 64 i).toNat = base.toNat + i := by
    simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64,
      Nat.mod_eq_of_lt hsum]
  simpa [ha] using heap_load_byte base (base + BitVec.ofNat 64 i) bytes.toArray w frame
    hv (by omega) (by simpa [ha] using hi)

theorem Reads.take {m ptr bytes} (h : Reads m ptr bytes) (n : Nat) :
    Reads m ptr (bytes.take n) := by
  intro i hi
  have hb : i < bytes.length := by simp only [List.length_take] at hi; omega
  simpa using h i hb

theorem shift_or_byte (x y : Word) (hy : y < 256) :
    (x <<< (8 : Nat) ||| y) = x * 256 + y := by
  have hyNat : y.toNat < 2^8 := hy
  have hn := Nat.shiftLeft_add_eq_or_of_lt hyNat x.toNat
  have he := congrArg (BitVec.ofNat 64) hn
  simp only [Nat.shiftLeft_eq, BitVec.ofNat_or, BitVec.ofNat_add, BitVec.ofNat_mul,
    BitVec.ofNat_toNat] at he
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  exact he.symm

theorem byte_word_bound (b : UInt8) : BitVec.ofNat 64 b.toNat < (256 : Word) := by
  have h := b.toNat_lt
  simp [BitVec.lt_def, BitVec.toNat_ofNat]
  omega

def foldBytes (bytes : List UInt8) (acc : Word) : Word :=
  bytes.foldl (fun a b => a <<< (8 : Nat) ||| BitVec.ofNat 64 b.toNat) acc

end Libp2pAsm.Rv64.Logic
