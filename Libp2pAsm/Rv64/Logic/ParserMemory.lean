import Libp2pAsm.Rv64.Logic.WordMemory
import Libp2pAsm.Rv64.Logic.Bytes

namespace Libp2pAsm.Rv64.Logic.Parser
open Rv64.Logic

set_option backward.isDefEq.respectTransparency false

/-- A byte view inside any mapped region, independent of executable loads. -/
structure BytesAtRegion (m : Memory) (ptr : Word) (bytes : List UInt8) (index : Nat) : Prop where
  present : index < m.regions.size
  lower : m.regions[index].base.toNat ≤ ptr.toNat
  fits : ptr.toNat - m.regions[index].base.toNat + bytes.length ≤ m.regions[index].bytes.size
  nonwrap : ptr.toNat + bytes.length ≤ 2^64
  contents : ∀ i (hi : i < bytes.length),
    m.regions[index].bytes[ptr.toNat - m.regions[index].base.toNat + i]'(by omega) = bytes[i]

def BytesAt (m : Memory) (ptr : Word) (bytes : List UInt8) : Prop :=
  ∃ index, BytesAtRegion m ptr bytes index

theorem BytesAt.nonwrap {m ptr bytes} (h : BytesAt m ptr bytes) :
    ptr.toNat + bytes.length ≤ 2^64 := by
  obtain ⟨_, h⟩ := h
  exact h.nonwrap

theorem byte_locate {m : Memory} {addr : Word} {index : Nat}
    (hv : m.valid = true) (hp : index < m.regions.size)
    (hl : m.regions[index].base.toNat ≤ addr.toNat)
    (hb : addr.toNat - m.regions[index].base.toNat < m.regions[index].bytes.size) :
    m.regions.findIdx? (fun r => r.contains 1 addr) = some index := by
  apply Array.findIdx?_eq_some_iff_getElem.mpr
  refine ⟨hp, ?_, ?_⟩
  · simp [Region.contains, hl]; omega
  · intro j hj hc
    have hdis : (m.regions[j]'(by omega)).disjoint (m.regions[index]'hp) := by
      have pair : m.regions.toList.Pairwise Region.disjoint := by
        simp only [Memory.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
        exact hv.2
      have hh := List.pairwise_iff_getElem.mp pair j index
        (by simpa using Nat.lt_trans hj hp) (by simpa using hp) hj
      simpa only [Array.getElem_toList] using hh
    simp only [Region.contains, decide_eq_true_eq] at hc
    unfold Region.disjoint Region.endAddr at hdis
    omega

theorem BytesAt.reads {m ptr bytes} (h : BytesAt m ptr bytes) (hv : m.valid = true) :
    Reads m ptr bytes := by
  obtain ⟨index, h⟩ := h
  have hp := h.present
  intro i hi
  have ha : (ptr + BitVec.ofNat 64 i).toNat = ptr.toNat+i := by
    have hb := h.nonwrap
    simp [BitVec.toNat_add, Nat.mod_eq_of_lt (show i < 2^64 by omega),
      Nat.mod_eq_of_lt (show ptr.toNat+i < 2^64 by omega)]
  have hl := h.lower
  have hb := h.fits
  have hf := byte_locate hv h.present
    (show m.regions[index].base.toNat ≤ (ptr+BitVec.ofNat 64 i).toNat by omega)
    (show (ptr+BitVec.ofNat 64 i).toNat-m.regions[index].base.toNat <
      m.regions[index].bytes.size by omega)
  unfold Memory.load
  unfold_internal Libp2pAsm.Rv64.Memory.locate
  unfold_internal Libp2pAsm.Rv64.supportedWidth
  simp only [hv, Nat.mod_one, hf, h.present]
  simp [bind, Except.bind, pure, Except.pure, hp, ha]
  unfold_internal Libp2pAsm.Rv64.readBytes
  have he : ptr.toNat+i-m.regions[index].base.toNat =
      ptr.toNat-m.regions[index].base.toNat+i := by omega
  simp [List.range_succ, ha, he, h.present, h.contents i hi,
    show ptr.toNat-m.regions[index].base.toNat+i < m.regions[index].bytes.size by omega,
    bind, Except.bind, pure, Except.pure]

/-- Last-byte comparison used by the frozen preflight, including end=2^64. -/
theorem range_iff (ptr len : Word) (hn : len ≠ 0) :
    len + (-1 : Word) ≤ (-1 : Word) - ptr ↔ ptr.toNat + len.toNat ≤ 2^64 := by
  rw [show (-1 : Word) = 18446744073709551615 by decide]
  have hp := ptr.isLt
  have hl := len.isLt
  have hz : len.toNat ≠ 0 := by
    intro hz; apply hn; apply BitVec.eq_of_toNat_eq; simpa using hz
  rw [BitVec.le_def, BitVec.toNat_add, BitVec.toNat_sub]
  change (len.toNat+18446744073709551615)%18446744073709551616 ≤
    (18446744073709551616-ptr.toNat+18446744073709551615)%18446744073709551616 ↔ _
  omega

end Libp2pAsm.Rv64.Logic.Parser
