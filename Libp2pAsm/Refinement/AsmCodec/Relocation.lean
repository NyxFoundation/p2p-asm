import Libp2pAsm.Rv64.Logic.RelocationTrace
import Libp2pAsm.Refinement.AsmCodec.QuicEntry
import Libp2pAsm.Refinement.AsmCodec.UnsignedEntry
import Libp2pAsm.Refinement.AsmCodec.QuicEncodeCorrect
import Libp2pAsm.Refinement.AsmCodec.UnsignedEncodeCorrect

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

/-- The static relocation check applies to the existing lowered arrays verbatim. -/
theorem codecs_leafLayout (p : Program)
    (hp : p = quicEncode ∨ p = quicDecode ∨ p = unsignedEncode ∨ p = unsignedDecode) :
    LeafLayout p := by
  rcases hp with rfl | rfl | rfl | rfl
  all_goals exact ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- Normalize only proof entry PC and ra. Input words, data addresses and heaps are unchanged. -/
def proofEntry (s : State) : State := atPC (s.setReg .x1 0) 65536

@[simp] theorem proofEntry_memory (s : State) : (proofEntry s).memory = s.memory := by
  simp [proofEntry]

@[simp] theorem proofEntry_get (s : State) (r : Reg) (hr : r ≠ .x1) :
    (proofEntry s).getReg r = s.getReg r := by
  by_cases hz : r = .x0 <;> simp [proofEntry, getReg_setReg, hr, hz]

@[simp] theorem proofEntry_ra (s : State) : (proofEntry s).getReg .x1 = 0 := by
  simp [proofEntry, getReg_setReg]

theorem setReg_ra_restore (s : State) :
    (s.setReg .x1 0).setReg .x1 (s.getReg .x1) = s := by
  simp [LeanAsm.Rv64.State.setReg, LeanAsm.Rv64.State.getReg, LeanAsm.Rv64.Reg.toNat]

theorem relocate_proofEntry (p : Program) (s : State) (base : Word)
    (hp : p.base = 65536) (hpc : s.pc = base) :
    relocateState p base (s.getReg .x1) (proofEntry s) = s := by
  have haddr : (65536 : Word) + (base - 65536) = base := by
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  simp only [relocateState, proofEntry, remap, setReg_atPC, atPC_atPC, pc_atPC,
    setReg_ra_restore, hp]
  have hz : (65536 : Word) ≠ 0 := by decide
  rw [relocatePC, if_neg hz, haddr, ← hpc, atPC_self]

theorem remap_callee {f : Word → Word} {ra : Word} {s t : State}
    (h : PreservesCallee s t) : PreservesCallee (remap f ra s) (remap f ra t) := by
  intro r hr
  have hn : r ≠ .x1 := by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simpa only [remap_get _ _ _ _ hn] using h r hr

theorem remap_decodePost {f : Word → Word} {ra : Word} {t : State}
    {result : Except Spec.Codec.Error Spec.Codec.Decoded} (h : DecodePost result t) :
    DecodePost result (remap f ra t) := by
  cases result <;> simpa [DecodePost, Output] using h

theorem remap_encodePost {f : Word → Word} {ra base : Word} {t : State}
    {result : Except Spec.Codec.Error (List UInt8)} {cap : Nat}
    {bytes : Array UInt8} {frame : List Region} (h : EncodePost result cap base bytes frame t) :
    EncodePost result cap base bytes frame (remap f ra t) := by
  simpa [EncodePost, Output] using h

/-- An embedded invocation's code ownership and ABI return conditions.
No SPEC success or execution result is a precondition. -/
structure Invocation (source whole : Program) (entry ra : Word) (start : Nat) (m : Memory) : Prop where
  image : ValidImage whole m
  placement : Placement source entry ra
  slice : CodeSlice whole (relocated source entry) start

/-- Actual execution, frame for ra, and containment of every PC before return. -/
structure Returns (whole leaf : Program) (ra : Word) (bound : Nat) (s : State) (done : Completed) : Prop where
  run : runUntil whole ra bound s = .ok done
  bounded : done.steps ≤ bound
  pc : done.state.pc = ra
  returnAddress : done.state.getReg .x1 = s.getReg .x1
  callee : PreservesCallee s done.state
  internal : ∀ k u, k < done.steps → Trace whole ra k s u → InCode leaf u.pc

theorem invocation_returns {p whole : Program} {entry : Word} {start n bound : Nat} {s t : State}
    (hp : p = quicEncode ∨ p = quicDecode ∨ p = unsignedEncode ∨ p = unsignedDecode)
    (hi : Invocation p whole entry (s.getReg .x1) start s.memory) (hpc : s.pc = entry)
    (hn : n ≤ bound) (ht : Trace p 0 n (proofEntry s) t) (hret : t.pc = 0) :
    Returns whole (relocated p entry) (s.getReg .x1) bound s
      ⟨relocateState p entry (s.getReg .x1) t, n⟩ := by
  have hpbase : p.base = 65536 := by rcases hp with rfl | rfl | rfl | rfl <;> rfl
  have hentry := relocate_proofEntry p s entry hpbase hpc
  have hleaf := ht.relocate (codecs_leafLayout p hp) hi.placement (proofEntry_ra s)
  rw [hentry] at hleaf
  have hwhole := hleaf.embed hi.slice hi.image.aligned hi.image.bounded
  have hfinish : (relocateState p entry (s.getReg .x1) t).pc = s.getReg .x1 := by
    simp [relocateState, hret, relocatePC]
  have hcallee := remap_callee (f := relocatePC (entry-p.base) (s.getReg .x1))
    (ra := s.getReg .x1) (codecs_callee_saved hp ht)
  change PreservesCallee (relocateState p entry (s.getReg .x1) (proofEntry s)) _ at hcallee
  rw [hentry] at hcallee
  exact ⟨hwhole.runUntil hfinish hi.image.valid bound hn, hn, hfinish,
    by simp [relocateState], hcallee,
    fun k u hk hprefix => hleaf.embed_prefix_inCode hi.slice hi.image.aligned
      hi.image.bounded hk hprefix⟩

theorem invocation_writes {p whole : Program} {entry : Word} {start lo hi n : Nat} {s t : State}
    (hp : p = quicEncode ∨ p = quicDecode ∨ p = unsignedEncode ∨ p = unsignedDecode)
    (hv : Invocation p whole entry (s.getReg .x1) start s.memory) (hpc : s.pc = entry)
    (ht : WriteTrace p 0 lo hi n (proofEntry s) t) :
    WriteTrace whole (s.getReg .x1) lo hi n s (relocateState p entry (s.getReg .x1) t) := by
  have hpbase : p.base = 65536 := by rcases hp with rfl | rfl | rfl | rfl <;> rfl
  have hleaf := ht.relocate (codecs_leafLayout p hp) hv.placement (proofEntry_ra s)
  rw [relocate_proofEntry p s entry hpbase hpc] at hleaf
  exact hleaf.embed hv.slice hv.image.aligned hv.image.bounded

end Libp2pAsm.Refinement.AsmCodec
