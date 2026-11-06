import Libp2pAsm.Refinement.AsmBuffer.Raw
import Libp2pAsm.Refinement.AsmCodec.EncodeArithmetic
import Libp2pAsm.Refinement.Buffer

namespace Libp2pAsm.Refinement.AsmBuffer

open Rv64 Rv64.Logic Spec.Abi

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def RawReference.toSpec (ref : RawReference) : BufferRef :=
  ⟨ref.slot.toNat, ref.generation.toNat, ref.offset.toNat, ref.length.toNat⟩

def RawRegion.toSpec (r : RawRegion) : RegisteredRegion :=
  ⟨r.generation.toNat, r.base.toNat, r.capacity.toNat,
    decide (r.flags &&& 1 ≠ 0), decide (r.flags &&& 2 ≠ 0)⟩

/-- Raw validation extends the typed SPEC only for malformed ABI representations.
Once a descriptor is selected, the existing SPEC supplies every semantic outcome. -/
def abiSpec (table count access : Word) (ref : RawReference) (r : RawRegion) : Except BufferError Span :=
  if 1 < access.toNat then .error .invalidRegion
  else if 2^59 ≤ count.toNat then .error .invalidRegion
  else if count.toNat ≤ ref.slot.toNat then .error .unknownRegion
  else if 2^64 ≤ table.toNat + 32*ref.slot.toNat then .error .invalidRegion
  else if 4 ≤ r.flags.toNat then .error .invalidRegion
  else Spec.Abi.resolveBuffer #[r.toSpec] { ref.toSpec with slot := 0 } (decide (access ≠ 0))

def specOutput : Except BufferError Span → Word × Word × Word
  | .error e => (BitVec.ofNat 64 e.code, 0, 0)
  | .ok span => (0, BitVec.ofNat 64 span.address, BitVec.ofNat 64 span.length)

theorem add_no_wrap (a b : Word) : a ≤ a+b ↔ a.toNat+b.toNat < 2^64 := by
  simp only [BitVec.le_def, BitVec.toNat_add]
  have := a.isLt
  have := b.isLt
  omega

theorem sub_toNat (a b : Word) (h : b ≤ a) : (a-b).toNat = a.toNat-b.toNat := by
  simp only [BitVec.le_def] at h
  simp only [BitVec.toNat_sub]
  have := a.isLt
  have := b.isLt
  omega

theorem slot_shift (slot count : Word) (hs : slot < count) (hc : count >>> (59 : Nat) = 0) :
    (slot <<< (5 : Nat)).toNat = 32*slot.toNat := by
  have hn := (AsmCodec.word_shift_zero_iff count 59).mp hc
  have hb : slot.toNat < 2^59 := by have : slot.toNat < count.toNat := hs; omega
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show slot.toNat*2^5 < 2^64 by omega)]
  omega

theorem selected_result (access : Word) (ref : RawReference) (r : RawRegion) :
    (if r.flags &&& 1 = 0 then (2, 0, 0)
    else if r.generation ≠ ref.generation then (2, 0, 0)
    else if r.capacity = 0 then (4, 0, 0)
    else if ¬r.base ≤ r.base+r.capacity then (4, 0, 0)
    else if access ≠ 0 ∧ r.flags &&& 2 = 0 then (5, 0, 0)
    else if ¬ref.length ≤ r.capacity then (3, 0, 0)
    else if ¬ref.offset ≤ r.capacity-ref.length then (3, 0, 0)
    else (0, r.base+ref.offset, ref.length)) =
      specOutput (Spec.Abi.resolveBuffer #[r.toSpec] { ref.toSpec with slot := 0 }
        (decide (access ≠ 0))) := by
  have hg := r.generation.isLt
  have hcap : r.capacity = 0 ↔ r.capacity.toNat = 0 := by simp [← BitVec.toNat_inj]
  have hgen : ref.generation.toNat = r.generation.toNat ↔ r.generation = ref.generation := by
    simp [BitVec.toNat_inj, eq_comm]
  have hvalid : r.toSpec.valid ↔ r.capacity ≠ 0 ∧ r.base ≤ r.base+r.capacity := by
    change (0 < r.capacity.toNat ∧ r.generation.toNat < 2^64 ∧
      r.base.toNat+r.capacity.toNat < 2^64) ↔ _
    simp only [add_no_wrap]
    constructor
    · rintro ⟨hc, _, hb⟩
      exact ⟨fun hz => by have := hcap.mp hz; omega, hb⟩
    · rintro ⟨hc, hb⟩
      exact ⟨Nat.pos_of_ne_zero (fun hz => hc (hcap.mpr hz)), hg, hb⟩
  simp only [Spec.Abi.resolveBuffer, Array.getElem?_eq_getElem (by simp : 0 < (#[r.toSpec]).size)]
  change _ = specOutput (if r.toSpec.active ≠ true then .error .staleRegion else
    if ref.generation.toNat ≠ r.generation.toNat then .error .staleRegion else
    if ¬r.toSpec.valid then .error .invalidRegion else
    if decide (access ≠ 0) = true ∧ r.toSpec.writable ≠ true then .error .readOnly else
    if r.capacity.toNat < ref.length.toNat then .error .bounds else
    if r.capacity.toNat-ref.length.toNat < ref.offset.toNat then .error .bounds else
    .ok ⟨r.base.toNat+ref.offset.toNat, ref.length.toNat⟩)
  simp only [hvalid]
  by_cases hl : ref.length ≤ r.capacity
  · have hsub := sub_toNat _ _ hl
    simp only [BitVec.ofNat_eq_ofNat] at *
    simp [RawRegion.toSpec, hgen, BitVec.le_def, hsub, specOutput, BufferError.code,
      BitVec.ofNat_add]
    repeat (any_goals (first | (simp_all [BitVec.le_def, BitVec.ofNat_add]) | split))
  · have hlt : r.capacity.toNat < ref.length.toNat := by change ¬ref.length.toNat ≤ r.capacity.toNat at hl; omega
    simp only [BitVec.ofNat_eq_ofNat] at *
    simp [RawRegion.toSpec, hgen, BitVec.le_def, hlt, specOutput, BufferError.code]
    repeat (any_goals (first | (simp_all [BitVec.le_def, BitVec.ofNat_add]) | split))

/-- All representable raw values, including malformed access/count/flags and wrapping addresses. -/
theorem raw_refines_spec (table count access : Word) (ref : RawReference) (r : RawRegion) :
    rawResult table count access ref r = specOutput (abiSpec table count access ref r) := by
  by_cases ha : access ≤ 1
  case neg =>
    have ha' : 1 < access.toNat := by change ¬access.toNat ≤ 1 at ha; omega
    simp only [BitVec.ofNat_eq_ofNat] at *
    simp [rawResult, abiSpec, ha, ha', specOutput, BufferError.code]
  have ha' : ¬1 < access.toNat := by have : access.toNat ≤ 1 := ha; omega
  by_cases hc : count >>> (59 : Nat) = 0
  case neg =>
    have hc' : 2^59 ≤ count.toNat := by have hh : ¬count.toNat < 2^59 := fun h => hc ((AsmCodec.word_shift_zero_iff count 59).mpr h); omega
    simp only [BitVec.ofNat_eq_ofNat] at *
    simp [rawResult, abiSpec, ha, ha', hc, hc', specOutput, BufferError.code]
  have hc' : ¬2^59 ≤ count.toNat := by have := (AsmCodec.word_shift_zero_iff count 59).mp hc; omega
  by_cases hs : ref.slot < count
  case neg =>
    have hs' : count.toNat ≤ ref.slot.toNat := by change ¬ref.slot.toNat < count.toNat at hs; omega
    simp only [BitVec.ofNat_eq_ofNat] at *
    simp [rawResult, abiSpec, ha, ha', hc, hc', hs, hs', specOutput, BufferError.code]
  have hs' : ¬count.toNat ≤ ref.slot.toNat := by have : ref.slot.toNat < count.toNat := hs; omega
  have shift := slot_shift ref.slot count hs hc
  have address : table ≤ table+(ref.slot <<< (5 : Nat)) ↔ table.toNat+32*ref.slot.toNat < 2^64 := by
    rw [add_no_wrap, shift]
  by_cases ht : table ≤ table+(ref.slot <<< (5 : Nat))
  case neg =>
    have ht' : 2^64 ≤ table.toNat+32*ref.slot.toNat := by have hh : ¬table.toNat+32*ref.slot.toNat < 2^64 := fun h => ht (address.mpr h); omega
    simp only [BitVec.ofNat_eq_ofNat] at *
    simp [rawResult, abiSpec, ha, ha', hc, hc', hs, hs', ht, ht', specOutput, BufferError.code]
  have ht' : ¬2^64 ≤ table.toNat+32*ref.slot.toNat := by have := address.mp ht; omega
  by_cases hf : r.flags >>> (2 : Nat) = 0
  case neg =>
    have hf' : 4 ≤ r.flags.toNat := by have hh : ¬r.flags.toNat < 2^2 := fun h => hf ((AsmCodec.word_shift_zero_iff r.flags 2).mpr h); omega
    simp only [BitVec.ofNat_eq_ofNat] at *
    simp [rawResult, abiSpec, ha, ha', hc, hc', hs, hs', ht, ht', hf, hf', specOutput, BufferError.code]
  have hf' : ¬4 ≤ r.flags.toNat := by have := (AsmCodec.word_shift_zero_iff r.flags 2).mp hf; omega
  have result := selected_result access ref r
  simp only [BitVec.ofNat_eq_ofNat] at *
  simpa [rawResult, abiSpec, ha, ha', hc, hc', hs, hs', ht, ht', hf, hf'] using result

/-- Selecting an owned descriptor is equivalent to the original table lookup,
including stale generation, invalid region, permissions and bounds failures. -/
theorem selected_table (regions : Array RegisteredRegion) (ref : RawReference) (r : RawRegion)
    (write : Bool) (h : regions[ref.slot.toNat]? = some r.toSpec) :
    Spec.Abi.resolveBuffer regions ref.toSpec write =
      Spec.Abi.resolveBuffer #[r.toSpec] { ref.toSpec with slot := 0 } write := by
  simp [Spec.Abi.resolveBuffer, RawReference.toSpec, h]

end Libp2pAsm.Refinement.AsmBuffer
