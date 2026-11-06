import Libp2pAsm.Rv64.Logic.WriteTrace

namespace Libp2pAsm.Rv64.Logic

/-- An empty actual-store interval implies complete memory equality. -/
theorem WriteTrace.empty_memory {p stop lo n s t} (h : WriteTrace p stop lo lo n s t) :
    t.memory = s.memory := by
  induction h with
  | nil => rfl
  | cons hn hf he hw tail ih =>
    exact ih.trans (execInstr_memory_frame hw.empty he)

end Libp2pAsm.Rv64.Logic
