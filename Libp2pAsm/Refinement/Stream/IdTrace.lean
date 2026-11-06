import Libp2pAsm.Refinement.Stream.Id

namespace Libp2pAsm.Refinement.Stream
open Rv64 Rv64.Logic

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def ordinalProgram : Program := ⟨0x10000, Asm.Stream.ordinal.flatten.toArray⟩

/-- Exact fetch/execute trace for arbitrary input word and arbitrary memory.
The only fixed addresses are the explicit code/return mapping in this theorem. -/
theorem ordinal_trace (s : State) (hra : s.getReg .x1 = 0x80000) :
    Trace ordinalProgram 0x80000 16 (atPC s 0x10000) (atPC (ordinalPost s) 0x80000) := by
  unfold ordinalPost ordinalCleared Asm.Stream.temps
  rw [← ordinal_shift]
  trace_step (.SRLI .x10 .x10 2)
  trace_step (.ADDI .x11 .x0 0)
  trace_step (.ADDI .x12 .x0 0)
  trace_step (.ADDI .x13 .x0 0)
  trace_step (.ADDI .x14 .x0 0)
  trace_step (.ADDI .x5 .x0 0)
  trace_step (.ADDI .x6 .x0 0)
  trace_step (.ADDI .x7 .x0 0)
  trace_step (.ADDI .x15 .x0 0)
  trace_step (.ADDI .x16 .x0 0)
  trace_step (.ADDI .x17 .x0 0)
  trace_step (.ADDI .x28 .x0 0)
  trace_step (.ADDI .x29 .x0 0)
  trace_step (.ADDI .x30 .x0 0)
  trace_step (.ADDI .x31 .x0 0)
  trace_step (.JALR .x0 .x1 0)
  exact .nil _

theorem ordinal_runUntil (s : State) (hra : s.getReg .x1 = 0x80000)
    (hv : ordinalProgram.valid s.memory = true) :
    runUntil ordinalProgram 0x80000 16 (atPC s 0x10000) =
      .ok ⟨atPC (ordinalPost s) 0x80000,16⟩ :=
  (ordinal_trace s hra).runUntil rfl hv 16 (by omega)

end Libp2pAsm.Refinement.Stream
