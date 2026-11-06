import Libp2pAsm.Asm.Quic.Recovery.Ack

namespace Libp2pAsm.Asm.Quic.Recovery
open Rv64 Crypto.Util

def receiveBytes : SAsm.Stmt := sequence [ready, selectPath (e 3),
  checkedAdd .x15 3 (q 3) (e 4), H 16 (e 2)]

def validatePath : SAsm.Stmt := sequence [ready, selectPath (e 3),
  needEq (q 1) (e 4) 6, Q 2 (n 1), H 16 (e 2)]

def challenge : SAsm.Stmt := sequence [ready, selectPath (e 3), needLt (e 2) (e 5) 2,
  eq (q 22) (n 1) (needLe (q 21) (e 2) 7),
  Q 20 (e 4), Q 21 (e 5), Q 22 (n 1), H 16 (e 2)]

def response : SAsm.Stmt := sequence [ready, selectPath (e 3), needEq (q 1) (e 4) 6,
  needEq (q 22) (n 1) 6, needEq (q 20) (e 5) 6, needLt (e 2) (q 21) 8,
  Q 2 (n 1), Q 22 (n 0), H 16 (e 2)]

def newPath : SAsm.Stmt := sequence [ready, needLt (e 3) (h 4) 2, pathAt (e 3),
  needEq (q 0) (n 0) 10, nonzero (e 4) 3, pathInit (e 4) (h 10), H 16 (e 2)]

def activatePath : SAsm.Stmt := sequence [ready, selectPath (e 3), needEq (q 1) (e 4) 6,
  needEq (q 2) (n 1) 10, H 21 (e 3), H 22 (n 0), H 16 (e 2)]

def handshake : SAsm.Stmt := sequence [ready, flag (e 3), flag (e 4), flag (e 5),
  needLe (h 18) (e 3) 2, needLe (h 19) (e 4) 2, needLe (h 20) (e 5) 2,
  needLe (e 4) (e 3) 2, H 18 (e 3), H 19 (e 4), H 20 (e 5), H 16 (e 2)]

def firePto : SAsm.Stmt := sequence [timer,
  needEq (.mem .x13 0) (n 11) 6, needEq (.mem .x13 3) (n 2) 6,
  needEq (.mem .x13 4) (e 3) 6, needEq (.mem .x13 1) (e 4) 6,
  needLe (e 3) (e 2) 2, needLt (h 22) (n 63) 3, selectPath (.mem .x13 5),
  needEq (q 29) (n 0) 7, H 22 (add (h 22) (n 1)),
  basePto (e 4), backoff, Q 29 (n 2), Q 30 (add (e 4) (n 1)), Q 25 (e 2), H 16 (e 2),
  O 0 (n 12), O 1 (e 4), O 3 (n 2), O 4 (e 2)]

/-- Full ledger interval check, not a caller-asserted persistent-congestion bit.
The O(N) loop is bounded by configured history and quantum admission. -/
def collapse : SAsm.Stmt := sequence [ready, selectPacket (e 3),
  needEq (p 0) (n 5) 10, needEq (p 6) (n 1) 10,
  nonzero (q 16) 10, needLt (q 17) (p 15) 10,
  O 1 (p 2), O 2 (p 15), selectPacket (e 4),
  needEq (p 0) (n 5) 10, needEq (p 6) (n 1) 10, needEq (p 2) (.mem .x13 1) 10,
  needLt (.mem .x13 2) (p 15) 10, O 4 (p 15),
  needLe (q 15) (n ((2^64-1)/4)) 3,
  maximum .x13 0 (mul (q 15) (n 4)) (n 1000000),
  checkedAdd .x13 0 (.mem .x13 0) (q 14), checkedAdd .x13 0 (.mem .x13 0) (h 62),
  saveMulDiv .x13 0 (.mem .x13 0) (n 3) (n 1),
  needLt (.mem .x13 0) (sub (.mem .x13 4) (.mem .x13 2)) 10,
  set .x17 (n 0), block [.LD .x31 .x11 96],
  .loop (.ltu .x17 .x31) (sequence [packetAt (.reg .x17),
    eq (p 16) (n 1) (eq (p 2) (.mem .x13 1)
      (le (.mem .x13 2) (p 15) (le (p 15) (.mem .x13 4) (needEq (p 0) (n 5) 10)))),
    set .x17 (add (.reg .x17) (n 1)), block [.LD .x31 .x11 96]]),
  needLt (q 28) (.mem .x13 4) 6, Q 8 (mul (q 24) (n 2)), Q 13 (q 12), Q 11 (n 0), Q 28 (.mem .x13 4),
  H 16 (e 2), sequence ((List.range 8).map fun w => O w (n 0))]

def installKeys : SAsm.Stmt := sequence [ready, needLt (e 3) (n 3) 2,
  spaceAt (e 3), needEq (z 1) (n 0) 10,
  block [.LD .x5 .x12 24, .ADDI .x6 .x0 1, .SLL .x6 .x6 .x5,
    .LD .x5 .x11 248, .OR .x5 .x5 .x6, .SD .x11 .x5 248], H 16 (e 2)]

end Libp2pAsm.Asm.Quic.Recovery
