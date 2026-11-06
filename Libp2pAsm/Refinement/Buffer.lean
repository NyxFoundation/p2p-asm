import Libp2pAsm.Spec.Abi.Buffer

namespace Libp2pAsm.Refinement

open Spec.Abi

/-- Validated bounds justify subtraction first and non-wrapping address addition afterward. -/
theorem buffer_bounds (base capacity offset length : Nat)
    (hrange : base + capacity < 2^64) (hlen : length ≤ capacity)
    (hoffset : offset ≤ capacity - length) :
    base + offset + length ≤ base + capacity ∧ base + offset < 2^64 := by
  omega

/-- Successful resolution implies live identity, permissions and the whole byte range. -/
theorem resolveBuffer_sound (regions : Array RegisteredRegion) (ref : BufferRef)
    (write : Bool) (span : Span) (h : resolveBuffer regions ref write = .ok span) :
    ∃ r, regions[ref.slot]? = some r ∧ r.active = true ∧ ref.generation = r.generation ∧
      r.valid ∧ (write = true → r.writable = true) ∧
      span.address = r.base + ref.offset ∧ span.length = ref.length ∧
      span.address + span.length ≤ r.base + r.capacity ∧ span.address < 2^64 := by
  unfold resolveBuffer at h
  split at h
  · contradiction
  · rename_i r lookup
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    cases h
    refine ⟨r, lookup, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
    all_goals simp_all [RegisteredRegion.valid]
    omega

end Libp2pAsm.Refinement
