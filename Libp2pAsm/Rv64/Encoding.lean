import Libp2pAsm.Rv64.Basic

namespace Libp2pAsm.Rv64

inductive EncodeError where
  | oddDisplacement
  deriving DecidableEq, BEq, Repr

private def regBits (r : Reg) (shift : Nat) : Nat := r.toNat <<< shift

private def rType (f7 f3 : Nat) (rd a b : Reg) : UInt32 :=
  ((f7 <<< 25) ||| regBits b 20 ||| regBits a 15 ||| (f3 <<< 12) |||
    regBits rd 7 ||| 0x33).toUInt32

private def iType (op f3 : Nat) (rd a : Reg) (imm : Nat) : UInt32 :=
  ((imm <<< 20) ||| regBits a 15 ||| (f3 <<< 12) ||| regBits rd 7 ||| op).toUInt32

private def sType (f3 : Nat) (a b : Reg) (off : BitVec 12) : UInt32 :=
  let n := off.toNat
  (((n >>> 5) <<< 25) ||| regBits b 20 ||| regBits a 15 ||| (f3 <<< 12) |||
    ((n &&& 31) <<< 7) ||| 0x23).toUInt32

private def bType (f3 : Nat) (a b : Reg) (off : BitVec 13) : Except EncodeError UInt32 :=
  let n := off.toNat
  if n % 2 != 0 then .error .oddDisplacement else .ok
    ((((n >>> 12) &&& 1) <<< 31) ||| (((n >>> 5) &&& 63) <<< 25) |||
      regBits b 20 ||| regBits a 15 ||| (f3 <<< 12) ||| (((n >>> 1) &&& 15) <<< 8) |||
      (((n >>> 11) &&& 1) <<< 7) ||| 0x63).toUInt32

private def jType (rd : Reg) (off : BitVec 21) : Except EncodeError UInt32 :=
  let n := off.toNat
  if n % 2 != 0 then .error .oddDisplacement else .ok
    ((((n >>> 20) &&& 1) <<< 31) ||| (((n >>> 1) &&& 1023) <<< 21) |||
      (((n >>> 11) &&& 1) <<< 20) ||| (((n >>> 12) &&& 255) <<< 12) |||
      regBits rd 7 ||| 0x6f).toUInt32

def encode : Instr → Except EncodeError UInt32
  | .ADD rd a b => .ok (rType 0 0 rd a b)
  | .SUB rd a b => .ok (rType 32 0 rd a b)
  | .AND rd a b => .ok (rType 0 7 rd a b)
  | .OR rd a b => .ok (rType 0 6 rd a b)
  | .XOR rd a b => .ok (rType 0 4 rd a b)
  | .SLL rd a b => .ok (rType 0 1 rd a b)
  | .SRL rd a b => .ok (rType 0 5 rd a b)
  | .SRA rd a b => .ok (rType 32 5 rd a b)
  | .SLT rd a b => .ok (rType 0 2 rd a b)
  | .SLTU rd a b => .ok (rType 0 3 rd a b)
  | .ADDI rd a imm => .ok (iType 0x13 0 rd a imm.toNat)
  | .ANDI rd a imm => .ok (iType 0x13 7 rd a imm.toNat)
  | .ORI rd a imm => .ok (iType 0x13 6 rd a imm.toNat)
  | .XORI rd a imm => .ok (iType 0x13 4 rd a imm.toNat)
  | .SLLI rd a n => .ok (iType 0x13 1 rd a n.toNat)
  | .SRLI rd a n => .ok (iType 0x13 5 rd a n.toNat)
  | .SRAI rd a n => .ok (iType 0x13 5 rd a (0x400 + n.toNat))
  | .LUI rd imm => .ok ((imm.toNat <<< 12 ||| regBits rd 7 ||| 0x37).toUInt32)
  | .AUIPC rd imm => .ok ((imm.toNat <<< 12 ||| regBits rd 7 ||| 0x17).toUInt32)
  | .MUL rd a b => .ok (rType 1 0 rd a b)
  | .MULHU rd a b => .ok (rType 1 3 rd a b)
  | .DIVU rd a b => .ok (rType 1 5 rd a b)
  | .REMU rd a b => .ok (rType 1 7 rd a b)
  | .LBU rd a off => .ok (iType 0x03 4 rd a off.toNat)
  | .LD rd a off => .ok (iType 0x03 3 rd a off.toNat)
  | .SB a b off => .ok (sType 0 a b off)
  | .SD a b off => .ok (sType 3 a b off)
  | .BEQ a b off => bType 0 a b off
  | .BNE a b off => bType 1 a b off
  | .BLTU a b off => bType 6 a b off
  | .BGEU a b off => bType 7 a b off
  | .JAL rd off => jType rd off
  | .JALR rd a off => .ok (iType 0x67 0 rd a off.toNat)

def encodeProgram (code : Array Instr) : Except EncodeError ByteArray := do
  let words ← code.mapM encode
  return words.foldl (fun bytes word =>
    (List.range 4).foldl (fun out i => out.push (word >>> (8 * i).toUInt32).toUInt8) bytes)
    ByteArray.empty

end Libp2pAsm.Rv64
