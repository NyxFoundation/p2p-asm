import Libp2pAsm.Asm.Buffer
import Libp2pAsm.Rv64.Logic.RelocationTrace
import Libp2pAsm.Rv64.Logic.WordMemory
import Libp2pAsm.Rv64.Logic.Complete

namespace Libp2pAsm.Refinement.AsmBuffer

open Rv64 Rv64.Logic

set_option maxRecDepth 8192

def program : Program := ⟨65536, Asm.resolveBuffer.flatten.toArray⟩

theorem lowered : Asm.resolveBuffer.lower = .ok program.code := by rfl

theorem leaf_layout : LeafLayout program := by
  exact ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem no_stores : ∀ i ∈ program.code, writesMemory i = false := by decide

theorem callee_saved {stop n s t} (h : Trace program stop n s t) : PreservesCallee s t := by
  intro r hr
  apply h.register_frame
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end Libp2pAsm.Refinement.AsmBuffer
