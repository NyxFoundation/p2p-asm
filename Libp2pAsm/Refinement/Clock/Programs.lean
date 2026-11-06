import Libp2pAsm.Asm.Clock
import Libp2pAsm.Spec.Clock
import Libp2pAsm.Rv64.Logic.RelocationTrace
import Libp2pAsm.Rv64.Logic.WordMemory
import Libp2pAsm.Rv64.Logic.WriteFrame

namespace Libp2pAsm.Refinement.Clock

open Rv64 Rv64.Logic

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def program : Program := ⟨65536, Asm.checkClock.flatten.toArray⟩

theorem lowered : Asm.checkClock.lower = .ok program.code := by rfl

theorem leaf_layout : LeafLayout program := by
  exact ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem callee_saved {stop n s t} (h : Trace program stop n s t) : PreservesCallee s t := by
  intro r hr
  apply h.register_frame
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end Libp2pAsm.Refinement.Clock
