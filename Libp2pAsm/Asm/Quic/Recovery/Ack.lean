import Libp2pAsm.Asm.Quic.Recovery.Timing

namespace Libp2pAsm.Asm.Quic.Recovery
open Rv64 Crypto.Util

def clearBatch : SAsm.Stmt := sequence [
  set .x14 rangesBase, set .x15 (mul (h 5) (n 16)), wipe .x14 .x15,
  sequence ([23,24,25,26,27,28,29,30,56,57,58,59,60].map fun w => H w (n 0))]

def beginAck : SAsm.Stmt := sequence [ready, selectSpace (e 3),
  needLt (e 4) (n (2^62)) 2, nonzero (e 5) 2, needLe (e 5) (h 5) 5,
  needLe (add (n 128) (mul (e 5) (n 16))) (.mem .x10 3) 5,
  clearBatch, H 23 (n 1), H 24 (e 3), H 25 (e 2), H 26 (e 4), H 27 (e 5), H 16 (e 2),
  set .x14 (add (.reg .x12) (n 128)), set .x15 rangesBase,
  set .x16 (n (2^62+1)), set .x17 (e 5),
  .loop (.ne .x17 .x0) (sequence [needLe (p 0) (p 1) 2,
    needLt (p 1) (n (2^62)) 2, needLt (add (p 1) (n 1)) (.reg .x16) 2,
    Q 0 (p 0), Q 1 (p 1), set .x16 (p 0),
    block [.ADDI .x14 .x14 16, .ADDI .x15 .x15 16, .ADDI .x17 .x17 (-1)]]),
  set .x15 rangesBase, H 30 (q 1), O 0 (n 10)]

def finishValidation : SAsm.Stmt := sequence [
  eq (h 29) (n 0) (sequence [clearBatch, commit]),
  eq (h 57) (n 1) (eq (h 58) (n 1) rtt),
  ne (add (h 17) (h 20)) (n 0) (H 22 (n 0)),
  spaceAt (h 24), maximum .x16 2 (z 2) (add (h 30) (n 1)), Z 7 (n 0),
  H 23 (n 3), H 28 (n 0), O 0 (n 10)]

def validateOne : SAsm.Stmt := sequence [
  eq (h 59) (h 27) (sequence [finishValidation, commit]),
  set .x15 (add rangesBase (mul (h 59) (n 16))),
  eq (h 28) (h 12) (sequence [needEq (h 60) (add (sub (q 1) (q 0)) (n 1)) 12,
    H 28 (n 0), H 60 (n 0), H 59 (add (h 59) (n 1)), O 0 (n 10), commit]),
  packetAt (h 28),
  eq (p 1) (h 24) (le (q 0) (p 3) (le (p 3) (q 1) (sequence [
    needEq (p 16) (n 1) 12, needLe (p 15) (h 25) 12, H 60 (add (h 60) (n 1)),
    eq (p 3) (h 30) (sequence [H 56 (h 28), ne (p 0) (n 4) (H 57 (n 1))]),
    ne (p 0) (n 4) (sequence [H 29 (n 1), eq (p 6) (n 1) (H 58 (n 1))])]))),
  H 28 (add (h 28) (n 1)), O 0 (n 10)]

def member : SAsm.Stmt := sequence [O 7 (n 0), set .x16 rangesBase, set .x17 (h 27),
  .loop (.ne .x17 .x0) (sequence [
    le (z 0) (p 3) (le (p 3) (z 1) (O 7 (n 1))),
    block [.ADDI .x16 .x16 16, .ADDI .x17 .x17 (-1)]])]

def ackPacket : SAsm.Stmt := sequence [pathAt (p 2), ackCC, Q 25 (h 25), spaceAt (p 1),
  eq (p 0) (n 3) (sequence [H 15 (sub (h 15) (n 1)),
    eq (p 6) (n 1) (Z 4 (sub (z 4) (n 1)))]),
  P 0 (n 4), packetAction 7 (h 28)]

def acknowledgeOne : SAsm.Stmt := sequence [
  eq (h 28) (h 12) (sequence [clearBatch, commit]),
  packetAt (h 28), O 0 (n 10),
  eq (p 1) (h 24) (ne (p 0) (n 4) (sequence [member,
    eq (.mem .x13 7) (n 1) ackPacket,
    eq (.mem .x13 0) (n 10) (O 7 (n 0))])),
  H 28 (add (h 28) (n 1))]

def testLoss : SAsm.Stmt := sequence [pathAt (p 2),
  maximum .x13 0 (q 12) (q 14), saveMulDiv .x13 0 (.mem .x13 0) (n 9) (n 8) true,
  maximum .x13 0 (.mem .x13 0) (n 1000000),
  checkedAdd .x13 4 (.mem .x13 0) (p 15), O 0 (n 10), O 7 (n 0),
  lt (add (p 3) (n 3)) (z 2) (O 7 (n 1)),
  le (.mem .x13 4) (h 25) (O 7 (n 1)),
  set .x17 (.mem .x13 7),
  eq (.reg .x17) (n 1) (sequence [lossCC, P 0 (n 5), H 15 (sub (h 15) (n 1)),
    eq (p 6) (n 1) (Z 4 (sub (z 4) (n 1))), packetAction 8 (h 28)]),
  eq (.reg .x17) (n 0) (sequence [
    eq (z 7) (n 0) (Z 7 (.mem .x13 4)), minimum .x16 7 (z 7) (.mem .x13 4),
    O 4 (n 0)])]

def lostOne : SAsm.Stmt := sequence [
  eq (h 28) (h 12) (sequence [
    eq (h 27) (n 0) (sequence [clearBatch, commit]),
    H 23 (n 2), H 28 (n 0), O 0 (n 10), commit]),
  packetAt (h 28), spaceAt (h 24), O 0 (n 10),
  eq (p 1) (h 24) (eq (p 0) (n 3) (lt (p 3) (z 2) (sequence [
    member, set .x17 (.mem .x13 7), O 7 (n 0), spaceAt (h 24),
    eq (.reg .x17) (n 0) testLoss]))),
  H 28 (add (h 28) (n 1))]

def beginLoss : SAsm.Stmt := sequence [ready, selectSpace (e 3),
  nonzero (z 7) 6, needLe (z 7) (e 2) 6, Z 7 (n 0), clearBatch,
  H 23 (n 3), H 24 (e 3), H 25 (e 2), H 16 (e 2), O 0 (n 10)]

def beginDiscard : SAsm.Stmt := sequence [ready, needLt (e 3) (n 2) 2, selectSpace (e 3),
  needEq (z 5) (n 0) 7, Z 1 (n 1), Z 3 (n 0), Z 7 (n 0), H 22 (n 0), clearBatch,
  set .x17 (n 0), block [.LD .x31 .x11 32],
  .loop (.ltu .x17 .x31) (sequence [pathAt (.reg .x17),
    eq (q 0) (n 1) (Q 25 (e 2)),
    eq (q 30) (add (e 3) (n 1)) (sequence [Q 29 (n 0), Q 30 (n 0)]),
    set .x17 (add (.reg .x17) (n 1)), block [.LD .x31 .x11 32]]),
  H 23 (n 4), H 24 (e 3), H 25 (e 2), H 16 (e 2), O 0 (n 10)]

def discardOne : SAsm.Stmt := sequence [
  eq (h 28) (h 12) (sequence [clearBatch, commit]), packetAt (h 28), O 0 (n 10),
  eq (p 1) (h 24) (eq (p 0) (n 3) (sequence [pathAt (p 2), spaceAt (p 1),
    eq (p 5) (n 1) (Q 6 (sub (q 6) (p 4))),
    eq (p 6) (n 1) (Z 4 (sub (z 4) (n 1))),
    H 15 (sub (h 15) (n 1)), P 0 (n 8), packetAction 9 (h 28)])),
  H 28 (add (h 28) (n 1))]

def resume : SAsm.Stmt := sequence [generation,
  eq (h 23) (n 1) (sequence [validateOne, commit]),
  eq (h 23) (n 2) (sequence [acknowledgeOne, commit]),
  eq (h 23) (n 3) (sequence [lostOne, commit]),
  eq (h 23) (n 4) (sequence [discardOne, commit]), done 10]

end Libp2pAsm.Asm.Quic.Recovery
