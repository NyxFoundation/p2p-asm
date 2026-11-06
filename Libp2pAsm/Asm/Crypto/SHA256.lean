import Libp2pAsm.Asm.Crypto.Whole

namespace Libp2pAsm.Asm.Crypto.SHA256

/-- One 64-byte SHA-256 block; state uses eight zero-extended LE64 slots.
Scratch and constants are each 512 bytes. See Sha2.compress for the full ABI. -/
def compress : Rv64.SAsm.Stmt := Sha2.compress .sha256

/-- Whole-message leaf; see Whole.hash for validation and memory contract. -/
def hash : Rv64.SAsm.Stmt := Whole.hash .sha256

end Libp2pAsm.Asm.Crypto.SHA256
