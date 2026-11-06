import Libp2pAsm.Rv64.State

namespace Libp2pAsm.Rv64

def writeReg (s : State) (rd : Reg) (value : Word) : Except Trap State :=
  .ok (s.setReg rd value).advance

def loadReg (s : State) (width : Nat) (rd rs1 : Reg) (offset : BitVec 12) :
    Except Trap State := do
  let value ← s.memory.load width (s.getReg rs1 + offset.signExtend 64)
  writeReg s rd value

def storeReg (s : State) (width : Nat) (rs1 rs2 : Reg) (offset : BitVec 12) :
    Except Trap State := do
  let memory ← s.memory.store width (s.getReg rs1 + offset.signExtend 64) (s.getReg rs2)
  return { s.advance with memory := memory }

def jump (s : State) (rd : Reg) (target : Word) : Except Trap State :=
  if target.toNat % 4 == 0 then
    .ok { s.setReg rd (s.pc + 4) with pc := target }
  else .error .instructionMisaligned

def branch (s : State) (taken : Bool) (offset : BitVec 13) : Except Trap State :=
  if taken then jump s .x0 (s.pc + offset.signExtend 64) else .ok s.advance

def execInstr (i : Instr) (s : State) : Except Trap State :=
  let get := s.getReg
  match i with
  | .ADD rd a b => writeReg s rd (get a + get b)
  | .SUB rd a b => writeReg s rd (get a - get b)
  | .AND rd a b => writeReg s rd (get a &&& get b)
  | .OR rd a b => writeReg s rd (get a ||| get b)
  | .XOR rd a b => writeReg s rd (get a ^^^ get b)
  | .SLL rd a b => writeReg s rd (get a <<< ((get b).toNat % 64))
  | .SRL rd a b => writeReg s rd (get a >>> ((get b).toNat % 64))
  | .SRA rd a b => writeReg s rd ((get a).sshiftRight ((get b).toNat % 64))
  | .SLT rd a b => writeReg s rd (if BitVec.slt (get a) (get b) then 1 else 0)
  | .SLTU rd a b => writeReg s rd (if get a < get b then 1 else 0)
  | .ADDI rd a imm => writeReg s rd (get a + imm.signExtend 64)
  | .ANDI rd a imm => writeReg s rd (get a &&& imm.signExtend 64)
  | .ORI rd a imm => writeReg s rd (get a ||| imm.signExtend 64)
  | .XORI rd a imm => writeReg s rd (get a ^^^ imm.signExtend 64)
  | .SLLI rd a n => writeReg s rd (get a <<< n.toNat)
  | .SRLI rd a n => writeReg s rd (get a >>> n.toNat)
  | .SRAI rd a n => writeReg s rd ((get a).sshiftRight n.toNat)
  | .LUI rd imm => writeReg s rd (((imm.zeroExtend 32) <<< 12).signExtend 64)
  | .AUIPC rd imm => writeReg s rd (s.pc + ((imm.zeroExtend 32 <<< 12).signExtend 64))
  | .MUL rd a b => writeReg s rd (get a * get b)
  | .MULHU rd a b => writeReg s rd (BitVec.ofNat 64 (((get a).toNat * (get b).toNat) / 2 ^ 64))
  | .DIVU rd a b => writeReg s rd (if get b == 0 then -1 else get a / get b)
  | .REMU rd a b => writeReg s rd (get a % get b)
  | .LBU rd a off => loadReg s 1 rd a off
  | .LD rd a off => loadReg s 8 rd a off
  | .SB a b off => storeReg s 1 a b off
  | .SD a b off => storeReg s 8 a b off
  | .BEQ a b off => branch s (get a == get b) off
  | .BNE a b off => branch s (get a != get b) off
  | .BLTU a b off => branch s (decide (get a < get b)) off
  | .BGEU a b off => branch s (decide (get b ≤ get a)) off
  | .JAL rd off => jump s rd (s.pc + off.signExtend 64)
  | .JALR rd a off => jump s rd ((get a + off.signExtend 64) &&& (~~~(1 : Word)))

def step (p : Program) (s : State) : Except Trap State := do
  execInstr (← p.fetch s.pc) s

/-- Execute a specified instruction sequence; fetch correspondence is a separate obligation. -/
def execSequence (code : List Instr) (s : State) : Except Trap State :=
  code.foldlM (fun state instruction => execInstr instruction state) s

structure Completed where
  state : State
  steps : Nat
  deriving Repr

/-- Fuel-indexed fetch/execute loop, exposed for kernel-checked execution proofs. -/
def runLoop (p : Program) (stop : Word) : Nat → State → Nat → Except Trap Completed
  | 0, s, count =>
    if s.pc == stop then .ok ⟨s, count⟩ else .error .fuelExhausted
  | remaining + 1, s, count => do
    if s.pc == stop then return ⟨s, count⟩
    runLoop p stop remaining (← step p s) (count + 1)

def runUntil (p : Program) (stop : Word) (fuel : Nat) (s : State) : Except Trap Completed :=
  if p.valid s.memory then runLoop p stop fuel s 0 else .error .invalidProgram

end Libp2pAsm.Rv64
