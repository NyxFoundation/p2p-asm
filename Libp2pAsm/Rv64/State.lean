import Libp2pAsm.Rv64.Memory
import Libp2pAsm.Rv64.Profile
import LeanAsm.Rv64.State

/-!
Register state and placed executable images delegated to LeanAsm. `Image` is
exposed under the local `Program` name; abbreviations resolve dot notation
natively and qualified references use the shared LeanAsm names.
-/

namespace Libp2pAsm.Rv64

abbrev State := LeanAsm.Rv64.State

/-- A fixed-width program placed at a concrete address for instruction fetch. -/
abbrev Program := LeanAsm.Rv64.Image

instance : LeanAsm.LowerRv64 Program where
  lower program := LeanAsm.lowerRv64 (program.code : Array Instr)

instance : LeanAsm.EmitAsm Program where
  emit name program := do
    let code ← LeanAsm.lowerRv64 (program.code : Array Instr)
    return LeanAsm.Rv64.emitProgram name code

end Libp2pAsm.Rv64
