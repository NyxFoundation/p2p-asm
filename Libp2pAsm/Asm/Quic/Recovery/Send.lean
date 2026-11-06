import Libp2pAsm.Asm.Quic.Recovery.Code

namespace Libp2pAsm.Asm.Quic.Recovery
open Rv64 Crypto.Util

def ampTest (bytes : E) (blocked : SAsm.Stmt) : SAsm.Stmt := eq (h 17) (n 1) (eq (q 2) (n 0) (sequence [
  block (bytes.emit 2 ++ [.LD .x5 .x15 32, .LD .x6 .x15 40] ++ carryInstructions ++ [
    .ADD .x5 .x28 .x7,
    .SLTU .x30 .x5 .x28, .ADD .x29 .x29 .x30,
    .LD .x6 .x15 24, .ADDI .x7 .x0 3, .MULHU .x31 .x6 .x7, .MUL .x30 .x6 .x7]),
  when (.ltu .x31 .x29) blocked,
  when (.eq .x31 .x29) (when (.ltu .x30 .x5) blocked)]))

def reserve : SAsm.Stmt := sequence [ready, selectSpace (e 3), selectPath (e 4),
  needEq (z 5) (n 0) 7, nonzero (e 5) 2, needLe (e 5) (q 24) 2,
  needLe (e 6) (n 15) 2,
  ne (.band (e 6) (n 2)) (n 0) (needEq (.band (e 6) (n 1)) (n 1) 2),
  needLt (z 0) (n (2^62)) 3, needLt (h 13) (n (2^64-1)) 3,
  needLt (h 12) (h 3) 5, needLt (h 14) (h 6) 7, needLt (h 15) (h 7) 7, ampTest (e 5) (done 7),
  ne (.band (e 6) (n 4)) (n 0) (sequence [
    nonzero (.band (e 6) (n 2)) 2, nonzero (q 29) 2, needEq (q 30) (add (e 3) (n 1)) 2, Q 29 (sub (q 29) (n 1))]),
  eq (.band (e 6) (n 5)) (n 1) (sequence [
    needLe (q 18) (e 2) 7, checkedAdd .x13 0 (q 6) (q 7),
    checkedAdd .x13 0 (.mem .x13 0) (e 5), needLe (.mem .x13 0) (q 8) 7]),
  packetAt (h 12), P 0 (n 1), P 1 (e 3), P 2 (e 4), P 3 (z 0), P 4 (e 5),
  P 5 (.band (e 6) (n 1)), P 6 (.band (.shr (e 6) (n 1)) (n 1)),
  P 7 (e 7), P 8 (e 8), P 9 (e 9), P 10 (e 10), P 11 (h 13), P 12 (n 1),
  P 13 (e 2), P 17 (e 2), checkedAdd .x14 14 (e 2) (h 9),
  P 18 (.band (.shr (e 6) (n 3)) (n 1)), P 19 (.band (.shr (e 6) (n 2)) (n 1)),
  checkedAdd .x15 5 (q 5) (e 5),
  eq (p 5) (n 1) (checkedAdd .x15 7 (q 7) (e 5)),
  Z 0 (add (z 0) (n 1)), Z 5 (add (h 12) (n 1)),
  packetAction 1 (h 12), H 12 (add (h 12) (n 1)), H 13 (add (h 13) (n 1)),
  H 14 (add (h 14) (n 1)), H 15 (add (h 15) (n 1)), H 16 (e 2)]

def release : SAsm.Stmt := sequence [Q 5 (sub (q 5) (p 4)),
  eq (p 5) (n 1) (Q 7 (sub (q 7) (p 4))), Z 5 (n 0),
  H 14 (sub (h 14) (n 1)), H 15 (sub (h 15) (n 1)), P 0 (n 6)]

def success : SAsm.Stmt := sequence [needLe (p 17) (e 6) 9, needLe (e 6) (e 2) 9,
  needLe (z 6) (p 3) 9,
  checkedAdd .x15 4 (q 4) (p 4),
  eq (p 5) (n 1) (checkedAdd .x15 6 (q 6) (p 4)),
  O 0 (n 0), eq (p 5) (n 1) (saveMulDiv .x13 0 (p 4) (q 14) (q 8) true),
  maximum .x15 18 (e 2) (q 18), checkedAdd .x15 18 (q 18) (.mem .x13 0),
  maximum .x15 19 (q 19) (e 6), Q 5 (sub (q 5) (p 4)),
  eq (p 5) (n 1) (Q 7 (sub (q 7) (p 4))),
  Z 5 (n 0), Z 6 (add (p 3) (n 1)),
  eq (p 6) (n 1) (sequence [Z 3 (e 6), Z 4 (add (z 4) (n 1))]),
  H 14 (sub (h 14) (n 1)), H 16 (e 2), P 0 (n 3), P 15 (e 6), P 16 (n 1),
  packetAction 2 (e 3)]

def result : SAsm.Stmt := sequence [ready, generation, selectPacket (e 3),
  needEq (p 0) (n 1) 6, needEq (p 11) (e 4) 6, needLt (e 2) (p 14) 8,
  needLe (e 5) (n 3) 2,
  eq (e 5) (n 0) success,
  eq (e 5) (n 1) (sequence [P 0 (n 2), packetAction 3 (e 3), H 16 (e 2)]),
  le (n 2) (e 5) (sequence [release, H 16 (e 2), packetAction 4 (e 3),
    eq (e 5) (n 2) (lt (n 1200) (p 4) (minimum .x15 24 (q 24) (sub (p 4) (n 1)))),
    eq (e 5) (n 3) (sequence [Q 23 (n 1), O 0 (n 5)]),
    le (p 4) (n 1200) (sequence [Q 23 (n 1), O 0 (n 5)])])]

def retry : SAsm.Stmt := sequence [ready, generation, selectPacket (e 3),
  needEq (p 0) (n 2) 10, needEq (q 23) (n 0) 10, needLt (e 2) (p 14) 8, needLt (p 12) (h 8) 8,
  needLt (h 13) (n (2^64-1)) 3, P 0 (n 1), P 11 (h 13), P 12 (add (p 12) (n 1)), P 17 (e 2),
  H 13 (add (h 13) (n 1)), H 16 (e 2), packetAction 1 (e 3)]

def expire : SAsm.Stmt := sequence [needEq (h 63) (n 0) 13, needLe (h 16) (e 2) 2, generation, selectPacket (e 3),
  needLe (n 1) (p 0) 6, needLe (p 0) (n 2) 6,
  lt (e 2) (p 14) (sequence [needEq (p 0) (n 2) 7, needLe (h 8) (p 12) 7]), H 16 (e 2), ne (h 23) (n 0) (H 63 (n 8)),
  eq (p 0) (n 1) (sequence [P 0 (n 7), H 63 (n 9), packetAction 6 (e 3)]),
  eq (p 0) (n 2) (sequence [release, Q 23 (n 1), packetAction 5 (e 3)])]

end Libp2pAsm.Asm.Quic.Recovery
