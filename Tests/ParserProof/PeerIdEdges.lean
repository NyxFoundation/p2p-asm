import Tests.ParserProof.PeerId

namespace Libp2pAsm.Tests.ParserProof.PeerId
open Rv64 Rv64.Logic Rv64.Logic.Parser Refinement.Identity.Peer

set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def errorCases : Array (Word × Word × Word × Word × Word × Spec.Identity.PublicKey.Error) :=
  #[(0,0,0,0,0,.keyType), (4294967297,0,32,0,38,.keyType),
    (2,0,32,0,0,.keyLength), (1,18446744073709551615,32,18446744073709551615,0,.capacity),
    (1,18446744073709551615,32,131073,38,.range), (1,196611,32,18446744073709551615,38,.range),
    (1,131073,32,131074,38,.range), (1,131074,32,131073,38,.range), (1,131073,32,131073,38,.range)]

theorem every_error_returns (i : Fin 9) :
    let c := errorCases[i]
    ∃ done, runUntil image 524288 384 (metadata c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1)=.ok done ∧
      ErrorOutput c.2.2.2.2.2.code done.state ∧
      AccessTrace image 524288 [] [] done.steps (metadata c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1) done.state ∧
      done.state.memory=(metadata c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1).memory := by
  apply rejected_without_mapping
  decide +revert

def edgeKey (i : Fin 2) : Word := if i=0 then 18446744073709551584 else 196611
def edgeOut (i : Fin 2) : Word := if i=0 then 131073 else 18446744073709551578
def edgeData : List UInt8 := List.replicate 32 0x7f
def edgeFrame (i : Fin 2) : List Region := [⟨edgeKey i,edgeData.toArray,false⟩]
def edgeState (i : Fin 2) : State := entry 1 (edgeKey i) 32 (edgeOut i) 38
  (heap (edgeOut i) (Array.replicate 38 0xcc) true (edgeFrame i))

theorem edge_owned (i : Fin 2) : InputAt (edgeState i) edgeData (Array.replicate 38 0xcc) (edgeFrame i) := by
  intro _
  refine ⟨rfl,rfl,?_,by decide,?_⟩
  · refine ⟨1,by change 1<2; decide,?_,?_,?_,?_⟩
    · change (edgeKey i).toNat≤(edgeKey i).toNat; omega
    · change (edgeKey i).toNat-(edgeKey i).toNat+32≤32; omega
    · exact (by decide : ∀ j : Fin 2,(edgeKey j).toNat+edgeData.length≤2^64) i
    · intro j hj
      change edgeData.toArray[(edgeKey i).toNat-(edgeKey i).toNat+j]'(by simp; exact hj)=edgeData[j]
      simp
  · exact (by decide : ∀ j : Fin 2,(edgeOut j).toNat+38≤2^64) i

/-- Both input and output may have exclusive end exactly 2^64. -/
theorem edge_returns (i : Fin 2) : ∃ done, runUntil image 524288 384 (edgeState i)=.ok done ∧
    done.state.getReg .x11=38 ∧ Clear done.state ∧
    done.state.memory=heap (edgeOut i) (patchBytes (Array.replicate 38 0xcc) 0 (canonical 1 edgeData)) true (edgeFrame i) ∧
    AccessTrace image 524288 (Refinement.AsmProtobuf.Footprint.byteReads (edgeKey i) 32)
      (Refinement.AsmProtobuf.Footprint.byteReads (edgeOut i) 38) done.steps (edgeState i) done.state := by
  have hv := invocation (edgeState i)
    ((by intro j; have hc : j=0 ∨ j=1 := by have := j.isLt; omega
         rcases hc with rfl | rfl <;> cbv : ∀ j : Fin 2,(edgeState j).memory.valid=true) i)
    (by intro r hr hw
        simp [edgeState,entry,heap,edgeFrame] at hr
        rcases hr with rfl | rfl
        · exact (by decide : ∀ j : Fin 2,
            (Region.mk (edgeOut j) (Array.replicate 38 0xcc) true).endAddr≤524288 ∨
              525040≤(edgeOut j).toNat) i
        · cases hw) rfl
  obtain ⟨done,hr,ho,hm,ht,_⟩ := peerId_embedded image 524292 1 (edgeState i) edgeData _ (edgeFrame i) hv rfl (edge_owned i)
  have he : rawError 1 (edgeKey i) 32 (edgeOut i) 38=none :=
    (by decide : ∀ j : Fin 2,rawError 1 (edgeKey j) 32 (edgeOut j) 38=none) i
  change Post (result 1 (edgeKey i) 32 (edgeOut i) 38 edgeData) done.state at ho
  change MemoryPost (edgeState i) done.state _ _ (result 1 (edgeKey i) 32 (edgeOut i) 38 edgeData) at hm
  change AccessTrace image 524288 (rawReads 1 (edgeKey i) 32 (edgeOut i) 38)
    (rawWrites 1 (edgeKey i) 32 (edgeOut i) 38) _ _ _ at ht
  simp only [result,he,Post] at ho
  simp only [result,he,MemoryPost] at hm
  simp only [rawReads,rawWrites,he] at ht
  exact ⟨done,hr.run,ho.1,ho.2,hm,ht⟩

end Libp2pAsm.Tests.ParserProof.PeerId
