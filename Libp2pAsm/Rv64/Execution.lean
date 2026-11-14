import Libp2pAsm.Rv64.State
import LeanAsm.Rv64.Execution

/-!
Executive semantics delegated to LeanAsm. Exports attach the shared
declarations to the local names, so step-by-step proof unfolding reaches the
same definitions.
-/

namespace Libp2pAsm.Rv64

export LeanAsm.Rv64 (writeReg loadReg storeReg jump branch execInstr
  execSequence execProgram step runLoop runUntil Completed)

end Libp2pAsm.Rv64
