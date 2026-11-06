import Libp2pAsm.Refinement.AsmCodec.Programs
import Libp2pAsm.Rv64.Logic.Frame

namespace Libp2pAsm.Refinement.AsmCodec

open Rv64 Rv64.Logic

/-- A finite static check over instructions, independent of all input values. -/
theorem codecs_destinations (p : Program)
    (hp : p = quicEncode ∨ p = quicDecode ∨ p = unsignedEncode ∨ p = unsignedDecode)
    (r : Reg) (hr : CalleeSaved r) : ∀ i ∈ p.code, r ≠ destination i := by
  rcases hp with rfl | rfl | rfl | rfl
  all_goals rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem codecs_callee_saved {p : Program} {stop : Word} {n : Nat} {s t : State}
    (hp : p = quicEncode ∨ p = quicDecode ∨ p = unsignedEncode ∨ p = unsignedDecode)
    (h : Trace p stop n s t) : PreservesCallee s t :=
  fun r hr => h.register_frame (codecs_destinations p hp r hr)

theorem codecs_return_address {p : Program} {stop : Word} {n : Nat} {s t : State}
    (hp : p = quicEncode ∨ p = quicDecode ∨ p = unsignedEncode ∨ p = unsignedDecode)
    (h : Trace p stop n s t) : t.getReg .x1 = s.getReg .x1 := by
  apply h.register_frame
  rcases hp with rfl | rfl | rfl | rfl <;> decide

theorem decoders_readonly (p : Program) (hp : p = quicDecode ∨ p = unsignedDecode) :
    ∀ i ∈ p.code, writesMemory i = false := by
  rcases hp with rfl | rfl <;> decide

theorem decoders_memory_frame {p : Program} {stop : Word} {n : Nat} {s t : State}
    (hp : p = quicDecode ∨ p = unsignedDecode) (h : Trace p stop n s t) :
    t.memory = s.memory := h.memory_frame (decoders_readonly p hp)

end Libp2pAsm.Refinement.AsmCodec
