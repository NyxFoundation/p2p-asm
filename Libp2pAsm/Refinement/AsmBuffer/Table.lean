import Libp2pAsm.Refinement.AsmBuffer.Contract

namespace Libp2pAsm.Refinement.AsmBuffer

open Rv64 Rv64.Logic Spec.Abi AsmCodec

/-- The raw count and selected descriptor represent the caller-owned logical table.
Malformed counts are rejected before the table is interpreted. -/
def TableModel (regions : Array RegisteredRegion) (count : Word) (ref : RawReference) (r : RawRegion) : Prop :=
  count >>> (59 : Nat) = 0 → count.toNat = regions.size ∧
    (ref.slot.toNat < regions.size → regions[ref.slot.toNat]? = some r.toSpec)

/-- Original table SPEC, preceded only by the raw ABI checks it cannot represent. -/
def tableSpec (regions : Array RegisteredRegion) (table count access : Word)
    (ref : RawReference) (r : RawRegion) : Except BufferError Span :=
  if 1 < access.toNat then .error .invalidRegion
  else if 2^59 ≤ count.toNat then .error .invalidRegion
  else if count.toNat ≤ ref.slot.toNat then Spec.Abi.resolveBuffer regions ref.toSpec (decide (access ≠ 0))
  else if 2^64 ≤ table.toNat+32*ref.slot.toNat then .error .invalidRegion
  else if 4 ≤ r.flags.toNat then .error .invalidRegion
  else Spec.Abi.resolveBuffer regions ref.toSpec (decide (access ≠ 0))

theorem abiSpec_table (regions : Array RegisteredRegion) (table count access : Word)
    (ref : RawReference) (r : RawRegion) (h : TableModel regions count ref r) :
    abiSpec table count access ref r = tableSpec regions table count access ref r := by
  unfold abiSpec tableSpec
  split
  · rfl
  · split
    · rfl
    · rename_i hc
      have hc' : count >>> (59 : Nat) = 0 :=
        (AsmCodec.word_shift_zero_iff count 59).mpr (by omega)
      obtain ⟨hcount, hlookup⟩ := h hc'
      split
      · rename_i hs
        have hn : regions[ref.slot.toNat]? = none := Array.getElem?_eq_none (by omega)
        simp [Spec.Abi.resolveBuffer, RawReference.toSpec, hn]
      · rename_i hs
        rw [selected_table regions ref r _ (hlookup (by omega))]

def RegionMapped (m : Memory) (r : RegisteredRegion) : Prop :=
  ∃ i : Fin m.regions.size, m.regions[i].base.toNat ≤ r.base ∧
    r.base+r.capacity ≤ m.regions[i].endAddr ∧ (r.writable = true → m.regions[i].writable = true)

def RegistryMapped (m : Memory) (regions : Array RegisteredRegion) : Prop :=
  ∀ r ∈ regions, r.valid → r.active = true → RegionMapped m r

def SpanMapped (m : Memory) (span : Span) (write : Bool) : Prop :=
  ∃ i : Fin m.regions.size, m.regions[i].base.toNat ≤ span.address ∧
    span.address+span.length ≤ m.regions[i].endAddr ∧
    (write = true → m.regions[i].writable = true)

theorem resolved_mapping {m : Memory} {regions : Array RegisteredRegion} {ref : BufferRef}
    {write : Bool} {span : Span} (hm : RegistryMapped m regions)
    (h : Spec.Abi.resolveBuffer regions ref write = .ok span) : SpanMapped m span write := by
  obtain ⟨r, hlookup, hactive, _, hvalid, hwrite, haddr, _, hbound, _⟩ := resolveBuffer_sound regions ref write span h
  have hmem : r ∈ regions := Array.mem_of_getElem? hlookup
  obtain ⟨i, hlo, hhi, hw⟩ := hm r hmem hvalid hactive
  exact ⟨i, by omega, by omega, fun h => hw (hwrite h)⟩

theorem tableSpec_success {regions table count access ref r span}
    (h : tableSpec regions table count access ref r = .ok span) :
    Spec.Abi.resolveBuffer regions ref.toSpec (decide (access ≠ 0)) = .ok span := by
  unfold tableSpec at h
  repeat (any_goals (first | exact h | contradiction | split at h))

/-- Full table refinement, with caller-owned mappings and no resolution-success premise. -/
theorem resolve_table_embedded (whole : Program) (entry : Word) (start : Nat)
    (s : State) (regions : Array RegisteredRegion) (ref : RawReference) (r : RawRegion)
    (hi : Invocation program whole entry (s.getReg .x1) start s.memory) (hpc : s.pc = entry)
    (href : ReferenceAt s.memory (s.getReg .x11) ref)
    (hregion : RegionAt s.memory (s.getReg .x10) (s.getReg .x12) (s.getReg .x13) ref r)
    (htable : TableModel regions (s.getReg .x12) ref r) (hmapped : RegistryMapped s.memory regions) :
    ∃ done, Returns whole (relocated program entry) (s.getReg .x1) 96 s done ∧
      RawPost (specOutput (tableSpec regions (s.getReg .x10) (s.getReg .x12) (s.getReg .x13) ref r)) done.state ∧
      done.state.memory = s.memory ∧ WriteTrace whole (s.getReg .x1) 0 0 done.steps s done.state ∧
      (∀ span, tableSpec regions (s.getReg .x10) (s.getReg .x12) (s.getReg .x13) ref r = .ok span →
        SpanMapped done.state.memory span (decide (s.getReg .x13 ≠ 0))) := by
  obtain ⟨done, hr, hp, hm, hw⟩ := resolve_embedded whole entry start s ref r hi hpc href hregion
  rw [abiSpec_table regions _ _ _ ref r htable] at hp
  refine ⟨done, hr, hp, hm, hw, ?_⟩
  intro span hspan
  rw [hm]
  exact resolved_mapping hmapped (tableSpec_success hspan)

end Libp2pAsm.Refinement.AsmBuffer
