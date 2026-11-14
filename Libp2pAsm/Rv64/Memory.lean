import Libp2pAsm.Rv64.Vocabulary
import LeanAsm.Rv64.Memory

/-!
Region memory delegated to LeanAsm. The abbreviations resolve dot notation
natively; qualified references use the shared LeanAsm names so that both
spellings unfold into the same definitions.
-/

namespace Libp2pAsm.Rv64

abbrev Region := LeanAsm.Rv64.Region

abbrev Memory := LeanAsm.Rv64.Memory

export LeanAsm.Rv64 (supportedWidth readBytes writeBytes)

end Libp2pAsm.Rv64
