import Libp2pAsm.Asm.Identity.PublicKey
import Libp2pAsm.Refinement.Identity.Canonical
import Libp2pAsm.Refinement.AsmDer.EncodeContract

namespace Libp2pAsm.Refinement.Identity.Peer
open Rv64 Rv64.Logic Rv64.Logic.Parser

set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def program : Program := ⟨65536,Asm.Identity.PublicKey.peerId.flatten.toArray⟩

theorem lowered : Asm.Identity.PublicKey.peerId.lower=.ok program.code := by rfl

theorem leaf_layout : LeafLayout program :=
  ⟨by decide,by decide,by decide,by decide,by decide⟩

theorem callee_saved {stop n s t} (h : Trace program stop n s t) : PreservesCallee s t := by
  intro r hr
  apply h.register_frame
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem platform_registers {stop n s t} (h : Trace program stop n s t) :
    t.getReg .x3=s.getReg .x3 ∧ t.getReg .x4=s.getReg .x4 := by
  constructor <;> apply h.register_frame <;> decide

end Libp2pAsm.Refinement.Identity.Peer
