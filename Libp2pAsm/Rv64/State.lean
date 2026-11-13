import Libp2pAsm.Rv64.Memory

namespace Libp2pAsm.Rv64

structure State where
  regs : Vector Word 32 := Vector.replicate 32 0
  pc : Word
  memory : Memory := {}
  deriving Repr

def State.getReg (s : State) (r : Reg) : Word :=
  if r = .x0 then 0 else s.regs[r.toNat]'r.toNat_lt

def State.setReg (s : State) (r : Reg) (value : Word) : State :=
  if r = .x0 then s else { s with regs := s.regs.set r.toNat value r.toNat_lt }

def State.advance (s : State) : State := { s with pc := s.pc + 4 }

structure Program where
  base : Word
  code : Array Instr
  deriving Repr

def Program.valid (p : Program) (memory : Memory) : Bool :=
  memory.valid && decide (p.base.toNat % 4 = 0 ∧ 0 < p.code.size ∧
    p.base.toNat + 4 * p.code.size ≤ 2 ^ 64) &&
    memory.regions.all (fun r => !r.writable || decide
      (r.endAddr ≤ p.base.toNat ∨ p.base.toNat + 4 * p.code.size ≤ r.base.toNat))

def Program.fetch (p : Program) (pc : Word) : Except Trap Instr := do
  unless pc.toNat % 4 == 0 do throw .instructionMisaligned
  unless p.base.toNat ≤ pc.toNat do throw .instructionBounds
  let offset := (pc.toNat - p.base.toNat) / 4
  if h : offset < p.code.size then return p.code[offset]
  else throw .instructionBounds

instance : LeanAsm.LowerRv64 Program where
  lower program := LeanAsm.lowerRv64 program.code

instance : LeanAsm.EmitAsm Program where
  emit name program := do
    let code ← LeanAsm.lowerRv64 program
    return LeanAsm.Rv64.emitProgram name code

end Libp2pAsm.Rv64
