import Libp2pAsm.Refinement.AsmBuffer.Execution

namespace Libp2pAsm.Refinement.AsmBuffer

open Rv64 Rv64.Logic

set_option maxRecDepth 8192
set_option maxHeartbeats 500000

/-- An unrepresentable table count is rejected without loading either pointer. -/
theorem invalid_count (s : State) (hra : s.getReg .x1 = 0)
    (ha : s.getReg .x13 ≤ 1) (hc : s.getReg .x12 >>> (59 : Nat) ≠ 0) :
    ∃ n t, n ≤ 96 ∧ Trace program 0 n (atPC s 65536) t ∧ t.pc = 0 ∧ RawPost (4, 0, 0) t := by
  buffer_finish 8

end Libp2pAsm.Refinement.AsmBuffer
