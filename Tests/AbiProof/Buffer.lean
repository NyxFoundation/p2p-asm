import Libp2pAsm.Refinement.AsmBuffer.Table
import Libp2pAsm.Refinement.AsmBuffer.Early
import Libp2pAsm.Codegen.Input

namespace Libp2pAsm.Tests.AbiProof

open Rv64 Rv64.Logic Refinement.AsmCodec Refinement.AsmBuffer Spec.Abi

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

structure Fixture where
  ref : RawReference := ⟨0, 7, 2, 3⟩
  region : RawRegion := ⟨7, 196608, 16, 3⟩
  count : Word := 1
  access : Word := 0
  table : Word := 131104

def metadata (f : Fixture) : Array UInt8 :=
  (Codegen.wordBytes [f.ref.slot, f.ref.generation, f.ref.offset, f.ref.length,
    f.region.generation, f.region.base, f.region.capacity, f.region.flags]).data

def entry (f : Fixture) : State :=
  let s : State := { pc := 524288, memory := heap 131072 (metadata f) true [⟨196608, Array.replicate 16 0xcc, true⟩] }
  (((s.setReg .x1 524800).setReg .x10 f.table).setReg .x11 131072).setReg .x12 f.count |>.setReg .x13 f.access

theorem metadata_size (f : Fixture) : (metadata f).size = 64 := by
  simp [metadata, Codegen.wordBytes, List.range_succ, List.foldl]

theorem fixture_invocation (f : Fixture) :
    Invocation program (relocated program 524288) 524288 ((entry f).getReg .x1) 0 (entry f).memory := by
  refine ⟨⟨?_, by decide, by decide, by decide, ?_⟩,
    ⟨by decide, by decide, ?_, ?_⟩, CodeSlice.refl _⟩
  · change (heap 131072 (metadata f) true [⟨196608, Array.replicate 16 0xcc, true⟩]).valid = true
    simp only [Memory.valid, Bool.and_eq_true]
    constructor
    · rw [Array.all_eq_true]
      intro i hi
      have he : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
      rcases he with rfl | rfl <;> simp [heap, Region.valid, Region.endAddr, metadata_size]
    · simp [heap, Region.disjoint, Region.endAddr, metadata_size]
  · intro r hr hw
    simp [entry, heap] at hr
    rcases hr with rfl | rfl <;> left <;> simp [Region.endAddr, metadata_size, relocated]
  · simp [entry, getReg_setReg]
  · right
    change 524288 + 4*program.code.size ≤ 524800
    decide



macro "own_word" : tactic => `(tactic| (
  refine ⟨0, ⟨by decide, by decide, by decide, by decide, by decide⟩⟩))

def successFixture : Fixture := {}

private theorem success_reference : ReferenceAt (entry successFixture).memory
    ((entry successFixture).getReg .x11) successFixture.ref := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

private theorem success_region : RegionAt (entry successFixture).memory
    ((entry successFixture).getReg .x10) ((entry successFixture).getReg .x12)
    ((entry successFixture).getReg .x13) successFixture.ref successFixture.region := by
  intro ha hc hs ht
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

theorem buffer_success : ∃ done,
    Returns (relocated program 524288) (relocated program 524288) 524800 96 (entry successFixture) done ∧
    RawPost (0, 196610, 3) done.state ∧ done.state.memory = (entry successFixture).memory ∧
    WriteTrace (relocated program 524288) 524800 0 0 done.steps (entry successFixture) done.state := by
  exact resolve_embedded (relocated program 524288) 524288 0 (entry successFixture)
    successFixture.ref successFixture.region (fixture_invocation _) rfl success_reference success_region

def unknownFixture : Fixture := { ref := ⟨1, 7, 2, 3⟩ }

private theorem unknown_reference : ReferenceAt (entry unknownFixture).memory
    ((entry unknownFixture).getReg .x11) unknownFixture.ref := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

private theorem unknown_region : RegionAt (entry unknownFixture).memory
    ((entry unknownFixture).getReg .x10) ((entry unknownFixture).getReg .x12)
    ((entry unknownFixture).getReg .x13) unknownFixture.ref unknownFixture.region := by
  intro ha hc hs ht
  have hn : ¬unknownFixture.ref.slot < (entry unknownFixture).getReg .x12 := by decide
  exact False.elim (hn hs)

theorem buffer_unknown : ∃ done,
    Returns (relocated program 524288) (relocated program 524288) 524800 96 (entry unknownFixture) done ∧
    RawPost (1, 0, 0) done.state ∧ done.state.memory = (entry unknownFixture).memory ∧
    WriteTrace (relocated program 524288) 524800 0 0 done.steps (entry unknownFixture) done.state := by
  exact resolve_embedded (relocated program 524288) 524288 0 (entry unknownFixture)
    unknownFixture.ref unknownFixture.region (fixture_invocation _) rfl unknown_reference unknown_region

def inactiveFixture : Fixture := { region := ⟨7, 196608, 16, 0⟩ }

private theorem inactive_reference : ReferenceAt (entry inactiveFixture).memory
    ((entry inactiveFixture).getReg .x11) inactiveFixture.ref := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

private theorem inactive_region : RegionAt (entry inactiveFixture).memory
    ((entry inactiveFixture).getReg .x10) ((entry inactiveFixture).getReg .x12)
    ((entry inactiveFixture).getReg .x13) inactiveFixture.ref inactiveFixture.region := by
  intro ha hc hs ht
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

theorem buffer_inactive : ∃ done,
    Returns (relocated program 524288) (relocated program 524288) 524800 96 (entry inactiveFixture) done ∧
    RawPost (2, 0, 0) done.state ∧ done.state.memory = (entry inactiveFixture).memory ∧
    WriteTrace (relocated program 524288) 524800 0 0 done.steps (entry inactiveFixture) done.state := by
  exact resolve_embedded (relocated program 524288) 524288 0 (entry inactiveFixture)
    inactiveFixture.ref inactiveFixture.region (fixture_invocation _) rfl inactive_reference inactive_region

def generationFixture : Fixture := { ref := ⟨0, 8, 2, 3⟩ }

private theorem generation_reference : ReferenceAt (entry generationFixture).memory
    ((entry generationFixture).getReg .x11) generationFixture.ref := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

private theorem generation_region : RegionAt (entry generationFixture).memory
    ((entry generationFixture).getReg .x10) ((entry generationFixture).getReg .x12)
    ((entry generationFixture).getReg .x13) generationFixture.ref generationFixture.region := by
  intro ha hc hs ht
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

theorem buffer_generation : ∃ done,
    Returns (relocated program 524288) (relocated program 524288) 524800 96 (entry generationFixture) done ∧
    RawPost (2, 0, 0) done.state ∧ done.state.memory = (entry generationFixture).memory ∧
    WriteTrace (relocated program 524288) 524800 0 0 done.steps (entry generationFixture) done.state := by
  exact resolve_embedded (relocated program 524288) 524288 0 (entry generationFixture)
    generationFixture.ref generationFixture.region (fixture_invocation _) rfl generation_reference generation_region

def boundsFixture : Fixture := { ref := ⟨0, 7, 2, 17⟩ }

private theorem bounds_reference : ReferenceAt (entry boundsFixture).memory
    ((entry boundsFixture).getReg .x11) boundsFixture.ref := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

private theorem bounds_region : RegionAt (entry boundsFixture).memory
    ((entry boundsFixture).getReg .x10) ((entry boundsFixture).getReg .x12)
    ((entry boundsFixture).getReg .x13) boundsFixture.ref boundsFixture.region := by
  intro ha hc hs ht
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

theorem buffer_bounds : ∃ done,
    Returns (relocated program 524288) (relocated program 524288) 524800 96 (entry boundsFixture) done ∧
    RawPost (3, 0, 0) done.state ∧ done.state.memory = (entry boundsFixture).memory ∧
    WriteTrace (relocated program 524288) 524800 0 0 done.steps (entry boundsFixture) done.state := by
  exact resolve_embedded (relocated program 524288) 524288 0 (entry boundsFixture)
    boundsFixture.ref boundsFixture.region (fixture_invocation _) rfl bounds_reference bounds_region

def empty_regionFixture : Fixture := { region := ⟨7, 196608, 0, 3⟩ }

private theorem empty_region_reference : ReferenceAt (entry empty_regionFixture).memory
    ((entry empty_regionFixture).getReg .x11) empty_regionFixture.ref := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

private theorem empty_region_region : RegionAt (entry empty_regionFixture).memory
    ((entry empty_regionFixture).getReg .x10) ((entry empty_regionFixture).getReg .x12)
    ((entry empty_regionFixture).getReg .x13) empty_regionFixture.ref empty_regionFixture.region := by
  intro ha hc hs ht
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

theorem buffer_empty_region : ∃ done,
    Returns (relocated program 524288) (relocated program 524288) 524800 96 (entry empty_regionFixture) done ∧
    RawPost (4, 0, 0) done.state ∧ done.state.memory = (entry empty_regionFixture).memory ∧
    WriteTrace (relocated program 524288) 524800 0 0 done.steps (entry empty_regionFixture) done.state := by
  exact resolve_embedded (relocated program 524288) 524288 0 (entry empty_regionFixture)
    empty_regionFixture.ref empty_regionFixture.region (fixture_invocation _) rfl empty_region_reference empty_region_region

def read_onlyFixture : Fixture := { region := ⟨7, 196608, 16, 1⟩, access := 1 }

private theorem read_only_reference : ReferenceAt (entry read_onlyFixture).memory
    ((entry read_onlyFixture).getReg .x11) read_onlyFixture.ref := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

private theorem read_only_region : RegionAt (entry read_onlyFixture).memory
    ((entry read_onlyFixture).getReg .x10) ((entry read_onlyFixture).getReg .x12)
    ((entry read_onlyFixture).getReg .x13) read_onlyFixture.ref read_onlyFixture.region := by
  intro ha hc hs ht
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

theorem buffer_read_only : ∃ done,
    Returns (relocated program 524288) (relocated program 524288) 524800 96 (entry read_onlyFixture) done ∧
    RawPost (5, 0, 0) done.state ∧ done.state.memory = (entry read_onlyFixture).memory ∧
    WriteTrace (relocated program 524288) 524800 0 0 done.steps (entry read_onlyFixture) done.state := by
  exact resolve_embedded (relocated program 524288) 524288 0 (entry read_onlyFixture)
    read_onlyFixture.ref read_onlyFixture.region (fixture_invocation _) rfl read_only_reference read_only_region

def bad_flagsFixture : Fixture := { region := ⟨7, 196608, 16, 4⟩ }

private theorem bad_flags_reference : ReferenceAt (entry bad_flagsFixture).memory
    ((entry bad_flagsFixture).getReg .x11) bad_flagsFixture.ref := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

private theorem bad_flags_region : RegionAt (entry bad_flagsFixture).memory
    ((entry bad_flagsFixture).getReg .x10) ((entry bad_flagsFixture).getReg .x12)
    ((entry bad_flagsFixture).getReg .x13) bad_flagsFixture.ref bad_flagsFixture.region := by
  intro ha hc hs ht
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

theorem buffer_bad_flags : ∃ done,
    Returns (relocated program 524288) (relocated program 524288) 524800 96 (entry bad_flagsFixture) done ∧
    RawPost (4, 0, 0) done.state ∧ done.state.memory = (entry bad_flagsFixture).memory ∧
    WriteTrace (relocated program 524288) 524800 0 0 done.steps (entry bad_flagsFixture) done.state := by
  exact resolve_embedded (relocated program 524288) 524288 0 (entry bad_flagsFixture)
    bad_flagsFixture.ref bad_flagsFixture.region (fixture_invocation _) rfl bad_flags_reference bad_flags_region

def bad_accessFixture : Fixture := { access := 2 }

private theorem bad_access_reference : ReferenceAt (entry bad_accessFixture).memory
    ((entry bad_accessFixture).getReg .x11) bad_accessFixture.ref := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

private theorem bad_access_region : RegionAt (entry bad_accessFixture).memory
    ((entry bad_accessFixture).getReg .x10) ((entry bad_accessFixture).getReg .x12)
    ((entry bad_accessFixture).getReg .x13) bad_accessFixture.ref bad_accessFixture.region := by
  intro ha hc hs ht
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

theorem buffer_bad_access : ∃ done,
    Returns (relocated program 524288) (relocated program 524288) 524800 96 (entry bad_accessFixture) done ∧
    RawPost (4, 0, 0) done.state ∧ done.state.memory = (entry bad_accessFixture).memory ∧
    WriteTrace (relocated program 524288) 524800 0 0 done.steps (entry bad_accessFixture) done.state := by
  exact resolve_embedded (relocated program 524288) 524288 0 (entry bad_accessFixture)
    bad_accessFixture.ref bad_accessFixture.region (fixture_invocation _) rfl bad_access_reference bad_access_region

def bad_countFixture : Fixture := { count := 576460752303423488 }

private theorem bad_count_reference : ReferenceAt (entry bad_countFixture).memory
    ((entry bad_countFixture).getReg .x11) bad_countFixture.ref := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

private theorem bad_count_region : RegionAt (entry bad_countFixture).memory
    ((entry bad_countFixture).getReg .x10) ((entry bad_countFixture).getReg .x12)
    ((entry bad_countFixture).getReg .x13) bad_countFixture.ref bad_countFixture.region := by
  intro ha hc hs ht
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

theorem buffer_bad_count : ∃ done,
    Returns (relocated program 524288) (relocated program 524288) 524800 96 (entry bad_countFixture) done ∧
    RawPost (4, 0, 0) done.state ∧ done.state.memory = (entry bad_countFixture).memory ∧
    WriteTrace (relocated program 524288) 524800 0 0 done.steps (entry bad_countFixture) done.state := by
  exact resolve_embedded (relocated program 524288) 524288 0 (entry bad_countFixture)
    bad_countFixture.ref bad_countFixture.region (fixture_invocation _) rfl bad_count_reference bad_count_region

def table_wrapFixture : Fixture := { ref := ⟨1, 7, 2, 3⟩, count := 2, table := 18446744073709551584 }

private theorem table_wrap_reference : ReferenceAt (entry table_wrapFixture).memory
    ((entry table_wrapFixture).getReg .x11) table_wrapFixture.ref := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

private theorem table_wrap_region : RegionAt (entry table_wrapFixture).memory
    ((entry table_wrapFixture).getReg .x10) ((entry table_wrapFixture).getReg .x12)
    ((entry table_wrapFixture).getReg .x13) table_wrapFixture.ref table_wrapFixture.region := by
  intro ha hc hs ht
  have hn : ¬(entry table_wrapFixture).getReg .x10 ≤
      (entry table_wrapFixture).getReg .x10 + (table_wrapFixture.ref.slot <<< (5 : Nat)) := by decide
  exact False.elim (hn ht)

theorem buffer_table_wrap : ∃ done,
    Returns (relocated program 524288) (relocated program 524288) 524800 96 (entry table_wrapFixture) done ∧
    RawPost (4, 0, 0) done.state ∧ done.state.memory = (entry table_wrapFixture).memory ∧
    WriteTrace (relocated program 524288) 524800 0 0 done.steps (entry table_wrapFixture) done.state := by
  exact resolve_embedded (relocated program 524288) 524288 0 (entry table_wrapFixture)
    table_wrapFixture.ref table_wrapFixture.region (fixture_invocation _) rfl table_wrap_reference table_wrap_region

def region_wrapFixture : Fixture := { region := ⟨7, 18446744073709551608, 16, 3⟩ }

private theorem region_wrap_reference : ReferenceAt (entry region_wrapFixture).memory
    ((entry region_wrapFixture).getReg .x11) region_wrapFixture.ref := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

private theorem region_wrap_region : RegionAt (entry region_wrapFixture).memory
    ((entry region_wrapFixture).getReg .x10) ((entry region_wrapFixture).getReg .x12)
    ((entry region_wrapFixture).getReg .x13) region_wrapFixture.ref region_wrapFixture.region := by
  intro ha hc hs ht
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

theorem buffer_region_wrap : ∃ done,
    Returns (relocated program 524288) (relocated program 524288) 524800 96 (entry region_wrapFixture) done ∧
    RawPost (4, 0, 0) done.state ∧ done.state.memory = (entry region_wrapFixture).memory ∧
    WriteTrace (relocated program 524288) 524800 0 0 done.steps (entry region_wrapFixture) done.state := by
  exact resolve_embedded (relocated program 524288) 524288 0 (entry region_wrapFixture)
    region_wrapFixture.ref region_wrapFixture.region (fixture_invocation _) rfl region_wrap_reference region_wrap_region

def empty_endFixture : Fixture := { ref := ⟨0, 7, 16, 0⟩ }

private theorem empty_end_reference : ReferenceAt (entry empty_endFixture).memory
    ((entry empty_endFixture).getReg .x11) empty_endFixture.ref := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

private theorem empty_end_region : RegionAt (entry empty_endFixture).memory
    ((entry empty_endFixture).getReg .x10) ((entry empty_endFixture).getReg .x12)
    ((entry empty_endFixture).getReg .x13) empty_endFixture.ref empty_endFixture.region := by
  intro ha hc hs ht
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> own_word

theorem buffer_empty_end : ∃ done,
    Returns (relocated program 524288) (relocated program 524288) 524800 96 (entry empty_endFixture) done ∧
    RawPost (0, 196624, 0) done.state ∧ done.state.memory = (entry empty_endFixture).memory ∧
    WriteTrace (relocated program 524288) 524800 0 0 done.steps (entry empty_endFixture) done.state := by
  exact resolve_embedded (relocated program 524288) 524288 0 (entry empty_endFixture)
    empty_endFixture.ref empty_endFixture.region (fixture_invocation _) rfl empty_end_reference empty_end_region

private theorem success_table : TableModel #[successFixture.region.toSpec]
    ((entry successFixture).getReg .x12) successFixture.ref successFixture.region := by
  intro hc
  exact ⟨rfl, fun _ => rfl⟩

private theorem success_registry : RegistryMapped (entry successFixture).memory
    #[successFixture.region.toSpec] := by
  intro r hr hv ha
  simp only [Array.mem_singleton] at hr
  subst r
  exact ⟨⟨1, by decide⟩, by decide, by decide, fun _ => rfl⟩

/-- The table theorem also certifies the returned span lies in an owned mapping. -/
theorem buffer_owned_span : ∃ done,
    Returns (relocated program 524288) (relocated program 524288) 524800 96 (entry successFixture) done ∧
    RawPost (0, 196610, 3) done.state ∧ done.state.memory = (entry successFixture).memory ∧
    WriteTrace (relocated program 524288) 524800 0 0 done.steps (entry successFixture) done.state ∧
    SpanMapped done.state.memory ⟨196610, 3⟩ false := by
  obtain ⟨done, hr, hp, hm, hw, hmap⟩ := resolve_table_embedded
    (relocated program 524288) 524288 0 (entry successFixture) #[successFixture.region.toSpec]
    successFixture.ref successFixture.region (fixture_invocation _) rfl
    success_reference success_region success_table success_registry
  exact ⟨done, hr, hp, hm, hw, hmap ⟨196610, 3⟩ rfl⟩

end Libp2pAsm.Tests.AbiProof
