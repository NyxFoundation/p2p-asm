import Libp2pAsm.Rv64.Basic
import LeanAsm.Rv64.Encoding

/-! Machine-code encoding delegated to LeanAsm under stable local names. -/

namespace Libp2pAsm.Rv64

abbrev EncodeError := LeanAsm.Rv64.EncodeError

namespace EncodeError
export LeanAsm.Rv64.EncodeError (oddDisplacement)
end EncodeError

export LeanAsm.Rv64 (encode encodeArray)

/-- Encode an instruction array into little-endian machine code. -/
def encodeProgram (code : Array Instr) : Except EncodeError ByteArray :=
  LeanAsm.Rv64.encodeArray code

end Libp2pAsm.Rv64
