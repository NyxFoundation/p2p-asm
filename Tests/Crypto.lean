import Tests.Crypto.SHA
import Tests.Crypto.HMAC
import Tests.Crypto.HKDF

namespace Libp2pAsm.Tests.Crypto

/-- Reference-specification tests only; no ASM implementation is exercised here. -/
def run : IO Unit := do
  runSHA
  runHMAC
  runHKDF

end Libp2pAsm.Tests.Crypto
