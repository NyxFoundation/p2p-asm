import Libp2pAsm.Rv64.Basic
import LeanAsm.Rv64.Encoding

/-! Machine-code encoding delegated to LeanAsm through the local ISA profile. -/

namespace Libp2pAsm.Rv64

abbrev EncodeError := LeanAsm.Rv64.EncodeError

namespace EncodeError
export LeanAsm.Rv64.EncodeError (oddDisplacement)
end EncodeError

def encode (instruction : Instr) : Except EncodeError UInt32 :=
  LeanAsm.Rv64.encode instruction.toLeanAsm

def encodeProgram (code : Array Instr) : Except EncodeError ByteArray := do
  let shared ← code.mapM (fun instruction => pure instruction.toLeanAsm)
  LeanAsm.Rv64.encodeArray shared

end Libp2pAsm.Rv64
