import Libp2pAsm.Rv64.Encoding

namespace Libp2pAsm.Codegen

open Rv64

def renderInstr : Instr → String
  | .ADD d a b => s!"add {d}, {a}, {b}" | .SUB d a b => s!"sub {d}, {a}, {b}"
  | .AND d a b => s!"and {d}, {a}, {b}" | .OR d a b => s!"or {d}, {a}, {b}"
  | .XOR d a b => s!"xor {d}, {a}, {b}" | .SLL d a b => s!"sll {d}, {a}, {b}"
  | .SRL d a b => s!"srl {d}, {a}, {b}" | .SRA d a b => s!"sra {d}, {a}, {b}"
  | .SLT d a b => s!"slt {d}, {a}, {b}" | .SLTU d a b => s!"sltu {d}, {a}, {b}"
  | .ADDI d a n => s!"addi {d}, {a}, {n.toInt}"
  | .ANDI d a n => s!"andi {d}, {a}, {n.toInt}"
  | .ORI d a n => s!"ori {d}, {a}, {n.toInt}"
  | .XORI d a n => s!"xori {d}, {a}, {n.toInt}"
  | .SLLI d a n => s!"slli {d}, {a}, {n.toNat}"
  | .SRLI d a n => s!"srli {d}, {a}, {n.toNat}"
  | .SRAI d a n => s!"srai {d}, {a}, {n.toNat}"
  | .LUI d n => s!"lui {d}, {n.toNat}"
  | .AUIPC d n => s!"auipc {d}, {n.toNat}"
  | .MUL d a b => s!"mul {d}, {a}, {b}"
  | .MULHU d a b => s!"mulhu {d}, {a}, {b}"
  | .DIVU d a b => s!"divu {d}, {a}, {b}"
  | .REMU d a b => s!"remu {d}, {a}, {b}"
  | .LBU d a off => s!"lbu {d}, {off.toInt}({a})"
  | .LD d a off => s!"ld {d}, {off.toInt}({a})"
  | .SB a b off => s!"sb {b}, {off.toInt}({a})"
  | .SD a b off => s!"sd {b}, {off.toInt}({a})"
  | .BEQ a b off => s!"beq {a}, {b}, . + ({off.toInt})"
  | .BNE a b off => s!"bne {a}, {b}, . + ({off.toInt})"
  | .BLTU a b off => s!"bltu {a}, {b}, . + ({off.toInt})"
  | .BGEU a b off => s!"bgeu {a}, {b}, . + ({off.toInt})"
  | .JAL d off => s!"jal {d}, . + ({off.toInt})"
  | .JALR d a off => s!"jalr {d}, {off.toInt}({a})"

def assembly (code : Array Instr) : String :=
  ".option norvc\n.option norelax\n.section .text.protocol, \"ax\", @progbits\n" ++
  ".balign 4\n.global protocol_entry\n.type protocol_entry, @function\nprotocol_entry:\n" ++
  String.join (code.toList.map (fun i => "  " ++ renderInstr i ++ "\n")) ++
  ".size protocol_entry, . - protocol_entry\n"

def byteHex (b : UInt8) : String :=
  let digits := "0123456789abcdef".toList.toArray
  String.ofList [digits[b.toNat / 16]!, digits[b.toNat % 16]!]

def hexBytes (bytes : ByteArray) : String :=
  String.join (bytes.data.toList.map byteHex)

end Libp2pAsm.Codegen
