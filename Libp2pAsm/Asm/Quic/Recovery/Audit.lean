import Libp2pAsm.Asm.Quic.Recovery.Context

namespace Libp2pAsm.Asm.Quic.Recovery
open Rv64 Crypto.Util

def clearOutput : SAsm.Stmt := sequence ((List.range 8).map fun i => O i (n 0))

def evidenceCheck : SAsm.Stmt := sequence [clearOutput, set .x17 (n 0), block [.LD .x31 .x11 96],
  .loop (.ltu .x17 .x31) (sequence [packetAt (.reg .x17),
    set .x16 (add (.reg .x13) (mul (p 1) (n 8))),
    needLe (z 0) (p 3) 10, Z 0 (add (p 3) (n 1)),
    eq (p 0) (n 1) (needEq (p 16) (n 0) 10),
    eq (p 0) (n 2) (needEq (p 16) (n 0) 10),
    eq (p 0) (n 6) (needEq (p 16) (n 0) 10),
    eq (p 0) (n 7) (needEq (p 16) (n 0) 10),
    eq (p 0) (n 3) (needEq (p 16) (n 1) 10),
    eq (p 0) (n 4) (needEq (p 16) (n 1) 10),
    eq (p 0) (n 5) (needEq (p 16) (n 1) 10),
    eq (p 0) (n 8) (needEq (p 16) (n 1) 10),
    set .x17 (add (.reg .x17) (n 1)), block [.LD .x31 .x11 96]]), clearOutput]

def sumPacket : SAsm.Stmt := sequence [
  eq (p 16) (n 1) (checkedAdd .x13 3 (.mem .x13 3) (p 4)),
  eq (p 0) (n 3) (eq (p 5) (n 1) (checkedAdd .x13 0 (.mem .x13 0) (p 4))),
  O 4 (n 0), le (p 0) (n 2) (O 4 (n 1)), eq (p 0) (n 7) (O 4 (n 1)),
  eq (.mem .x13 4) (n 1) (sequence [checkedAdd .x13 1 (.mem .x13 1) (p 4),
    eq (p 5) (n 1) (checkedAdd .x13 2 (.mem .x13 2) (p 4))])]

def pathTotals : SAsm.Stmt := sequence [set .x17 (n 0), block [.LD .x31 .x11 32],
  .loop (.ltu .x17 .x31) (sequence [pathAt (.reg .x17), clearOutput,
    needLe (q 0) (n 1) 10, needLe (q 2) (n 1) 10, needLe (q 11) (n 1) 10,
    needLe (q 22) (n 1) 10, needLe (q 23) (n 1) 10, needLe (q 29) (n 2) 10,
    eq (q 0) (n 1) (sequence [nonzero (q 1) 10, nonzero (q 8) 10,
      needLe (n 1200) (q 24) 10, needLe (q 24) (h 10) 10]),
    set .x16 (n 0), block [.LD .x31 .x11 96],
    .loop (.ltu .x16 .x31) (sequence [packetAt (.reg .x16),
      eq (p 2) (.reg .x17) (sequence [needEq (q 0) (n 1) 10, sumPacket]),
      set .x16 (add (.reg .x16) (n 1)), block [.LD .x31 .x11 96]]),
    needEq (q 6) (.mem .x13 0) 10, needEq (q 5) (.mem .x13 1) 10,
    needEq (q 7) (.mem .x13 2) 10, needEq (q 4) (.mem .x13 3) 10,
    set .x17 (add (.reg .x17) (n 1)), block [.LD .x31 .x11 32]]), clearOutput]

def connectionTotals : SAsm.Stmt := sequence [clearOutput, set .x17 (n 0), block [.LD .x31 .x11 96],
  .loop (.ltu .x17 .x31) (sequence [packetAt (.reg .x17), spaceAt (p 1),
    O 2 (n 0), le (p 0) (n 2) (O 2 (n 1)), eq (p 0) (n 7) (O 2 (n 1)),
    eq (.mem .x13 2) (n 1) (sequence [O 0 (add (.mem .x13 0) (n 1)),
      O 1 (add (.mem .x13 1) (n 1)), needEq (z 5) (add (.reg .x17) (n 1)) 10]),
    eq (p 0) (n 3) (O 1 (add (.mem .x13 1) (n 1))),
    set .x17 (add (.reg .x17) (n 1)), block [.LD .x31 .x11 96]]),
  needEq (h 14) (.mem .x13 0) 10, needEq (h 15) (.mem .x13 1) 10, clearOutput]

def spaceTotalsOne (i : Nat) : SAsm.Stmt := sequence [clearOutput,
  spaceAt (n i), set .x17 (n 0), block [.LD .x31 .x11 96],
  .loop (.ltu .x17 .x31) (sequence [packetAt (.reg .x17),
    eq (p 1) (n i) (sequence [
      eq (p 0) (n 3) (eq (p 6) (n 1) (O 0 (add (.mem .x13 0) (n 1)))),
      le (p 0) (n 2) (O 1 (add (.reg .x17) (n 1))),
      eq (p 0) (n 7) (O 1 (add (.reg .x17) (n 1))),
      eq (p 16) (n 1) (O 2 (add (p 3) (n 1)))]),
    set .x17 (add (.reg .x17) (n 1)), block [.LD .x31 .x11 96]]),
  needEq (z 4) (.mem .x13 0) 10, needEq (z 5) (.mem .x13 1) 10,
  needEq (z 6) (.mem .x13 2) 10, needLe (z 2) (z 6) 10, clearOutput]

def spaceTotals : SAsm.Stmt := sequence ((List.range 3).map spaceTotalsOne)

def batchCheck : SAsm.Stmt := sequence [
  eq (h 23) (n 1) (nonzero (h 27) 10),
  eq (h 57) (n 1) (needLt (h 56) (h 12) 10),
  set .x14 rangesBase, set .x16 (n (2^62+1)), set .x17 (h 27),
  .loop (.ne .x17 .x0) (sequence [needLe (p 0) (p 1) 10,
    needLt (p 1) (n (2^62)) 10, needLt (add (p 1) (n 1)) (.reg .x16) 10,
    set .x16 (p 0), block [.ADDI .x14 .x14 16, .ADDI .x17 .x17 (-1)]])]

end Libp2pAsm.Asm.Quic.Recovery
