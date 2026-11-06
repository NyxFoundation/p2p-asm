import Libp2pAsm.Rv64.Logic.Memory

namespace Libp2pAsm.Rv64.Logic

set_option backward.isDefEq.respectTransparency false

/-- Pure little-endian interpretation of eight owned bytes. -/
def readLE64 (bytes : Array UInt8) (offset : Nat) : Word :=
  (List.range 8).foldl (fun value i =>
    value ||| (BitVec.ofNat 64 (bytes[offset+i]?.getD 0).toNat <<< (8*i))) 0

/-- A structural memory representation, not a successful-load assumption. -/
structure WordAtRegion (m : Memory) (addr value : Word) (index : Nat) : Prop where
  present : index < m.regions.size
  aligned : addr.toNat % 8 = 0
  lower : m.regions[index].base.toNat ≤ addr.toNat
  fits : addr.toNat - m.regions[index].base.toNat + 8 ≤ m.regions[index].bytes.size
  bytes : value = readLE64 m.regions[index].bytes (addr.toNat - m.regions[index].base.toNat)

def WordAt (m : Memory) (addr value : Word) : Prop := ∃ index, WordAtRegion m addr value index

theorem wordAt_locate {m : Memory} {addr value : Word} {index : Nat}
    (hv : m.valid = true) (h : WordAtRegion m addr value index) :
    m.regions.findIdx? (fun r => r.contains 8 addr) = some index := by
  have hidx := h.present
  apply Array.findIdx?_eq_some_iff_getElem.mpr
  refine ⟨h.present, ?_, ?_⟩
  · simp [Region.contains, h.lower]; have := h.fits; omega
  · intro j hj hc
    have hdis : (m.regions[j]'(by omega)).disjoint (m.regions[index]'h.present) := by
      have hp : m.regions.toList.Pairwise Region.disjoint := by
        have hm := hv
        simp only [Memory.valid, Bool.and_eq_true, decide_eq_true_eq] at hm
        exact hm.2
      have hh := List.pairwise_iff_getElem.mp hp j index (by simpa using Nat.lt_trans hj h.present) (by simpa using h.present) hj
      simpa using hh
    simp only [Region.contains, decide_eq_true_eq] at hc
    have hl := h.lower
    have hb := h.fits
    unfold Region.disjoint Region.endAddr at hdis
    omega

theorem WordAt.load {m : Memory} {addr value : Word}
    (h : WordAt m addr value) (hv : m.valid = true) : m.load 8 addr = .ok value := by
  obtain ⟨index, h⟩ := h
  have hidx := h.present
  have hf := wordAt_locate hv h
  have hb := h.fits
  rw [h.bytes]
  unfold Memory.load
  unfold_internal Libp2pAsm.Rv64.Memory.locate
  unfold_internal Libp2pAsm.Rv64.supportedWidth
  simp only [hv, h.aligned, hf, h.present]
  simp [bind, Except.bind, pure, Except.pure]
  unfold_internal Libp2pAsm.Rv64.readBytes
  simp [hidx, readLE64, List.range_succ, bind, Except.bind, pure, Except.pure,
    show addr.toNat - m.regions[index].base.toNat < m.regions[index].bytes.size by omega,
    show addr.toNat - m.regions[index].base.toNat + 1 < m.regions[index].bytes.size by omega,
    show addr.toNat - m.regions[index].base.toNat + 2 < m.regions[index].bytes.size by omega,
    show addr.toNat - m.regions[index].base.toNat + 3 < m.regions[index].bytes.size by omega,
    show addr.toNat - m.regions[index].base.toNat + 4 < m.regions[index].bytes.size by omega,
    show addr.toNat - m.regions[index].base.toNat + 5 < m.regions[index].bytes.size by omega,
    show addr.toNat - m.regions[index].base.toNat + 6 < m.regions[index].bytes.size by omega,
    show addr.toNat - m.regions[index].base.toNat + 7 < m.regions[index].bytes.size by omega]

end Libp2pAsm.Rv64.Logic
