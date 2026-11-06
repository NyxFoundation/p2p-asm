import Libp2pAsm.Asm.Crypto.Whole

namespace Libp2pAsm.Asm.Crypto.SHA512

/-- One 128-byte SHA-512 block; state uses eight LE64 slots.
Scratch and constants are each 640 bytes. See Sha2.compress for the full ABI. -/
def compress : Rv64.SAsm.Stmt := Sha2.compress .sha512

/-- Whole-message leaf; see Whole.hash for validation and memory contract. -/
def hash : Rv64.SAsm.Stmt := Whole.hash .sha512

end Libp2pAsm.Asm.Crypto.SHA512
