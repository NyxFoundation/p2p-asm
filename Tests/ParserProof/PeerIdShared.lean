import Tests.ParserProof.PeerIdEdges

namespace Libp2pAsm.Tests.ParserProof.PeerId
open Rv64 Rv64.Logic Rv64.Logic.Parser Refinement.Identity.Peer

set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def sharedState : State := entry 1 131121 32 131073 38
  (heap 131073 (Array.replicate 84 0xcc) true [])
def sharedData : List UInt8 := List.replicate 32 0xcc

theorem shared_owned : InputAt sharedState sharedData (Array.replicate 84 0xcc) [] := by
  intro _
  refine ⟨rfl,rfl,?_,by decide,by decide⟩
  refine ⟨0,by decide,by decide,by decide,by decide,?_⟩
  intro i hi
  change i<32 at hi
  change (Array.replicate 84 (0xcc : UInt8))[48+i]'(by simp; omega)=(List.replicate 32 (0xcc : UInt8))[i]'(by simpa using hi)
  simp only [Array.getElem_replicate,List.getElem_replicate]

/-- Key and output are disjoint byte views in the same writable mapping. -/
theorem shared_returns : ∃ done, runUntil image 524288 384 sharedState=.ok done ∧
    done.state.getReg .x11=38 ∧ Clear done.state ∧
    done.state.memory=heap 131073
      (patchBytes (Array.replicate 84 0xcc) 0 (canonical 1 sharedData)) true [] ∧
    AccessTrace image 524288 (Refinement.AsmProtobuf.Footprint.byteReads 131121 32)
      (Refinement.AsmProtobuf.Footprint.byteReads 131073 38) done.steps sharedState done.state := by
  have hv := invocation sharedState (by cbv)
    (by intro r hr _; simp [sharedState,entry,heap] at hr; subst r; left; decide) rfl
  obtain ⟨done,hr,ho,hm,ht,_⟩ := peerId_embedded image 524292 1 sharedState sharedData _ [] hv rfl shared_owned
  exact ⟨done,hr.run,ho.1,ho.2,hm,ht⟩

end Libp2pAsm.Tests.ParserProof.PeerId
