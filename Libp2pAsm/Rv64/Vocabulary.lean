import LeanAsm.Rv64.Basic

/-!
Shared RV64 vocabulary imported from LeanAsm. This module contains no p2p
instruction-profile decisions.
-/

namespace Libp2pAsm.Rv64

abbrev Word := LeanAsm.Rv64.Word
abbrev Reg := LeanAsm.Rv64.Reg
abbrev Trap := LeanAsm.Rv64.Trap

namespace Reg
export LeanAsm.Rv64.Reg (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)
export LeanAsm.Rv64.Reg (x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
export LeanAsm.Rv64.Reg (zero ra sp gp tp t0 t1 t2 s0 fp s1 a0 a1 a2 a3 a4 a5 a6 a7)
export LeanAsm.Rv64.Reg (s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
def toNat (reg : Reg) : Nat := LeanAsm.Rv64.Reg.toNat reg
theorem toNat_lt (reg : Reg) : reg.toNat < 32 := by
  simpa [toNat] using LeanAsm.Rv64.Reg.toNat_lt reg
def toFin (reg : Reg) : Fin 32 := ⟨reg.toNat, reg.toNat_lt⟩
end Reg

namespace Trap
export LeanAsm.Rv64.Trap (memoryBounds memoryMisaligned readOnlyMemory invalidMemory)
export LeanAsm.Rv64.Trap (instructionBounds instructionMisaligned invalidProgram)
export LeanAsm.Rv64.Trap (unsupportedWidth fuelExhausted)
end Trap

end Libp2pAsm.Rv64
