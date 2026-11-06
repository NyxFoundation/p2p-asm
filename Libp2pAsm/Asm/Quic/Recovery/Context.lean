import Libp2pAsm.Asm.Quic.Recovery.Send

namespace Libp2pAsm.Asm.Quic.Recovery
open Rv64 Crypto.Util

def pathInit (gen mtu : E) : SAsm.Stmt := sequence [
  Q 0 (n 1), Q 1 gen, Q 9 (n (2^64-1)), Q 14 (n 333000000), Q 15 (n 166500000),
  Q 24 mtu, Q 25 (e 2), maximum .x15 8 (mul mtu (n 2)) (n 14720),
  minimum .x15 8 (q 8) (mul mtu (n 10))]

def layoutWords : E := add (add (add (n 64) (mul (h 4) (n 32)))
  (mul (h 3) (n 20))) (mul (h 5) (n 2))

/-- Limits are checked before any configured loop/address multiplication. The
capacity inequality is a conservative control-flow admission bound, not a measured
execution count or a machine-checked full recovery resource theorem. -/
def configCheck : SAsm.Stmt := sequence (
  ([3,4,5,6,7,8,9,11].map fun w => nonzero (h w) 5) ++
  [needLe (h 6) (h 7) 5, needLe (h 7) (h 3) 5,
   needLe (n 1200) (h 10) 5, needLe (h 10) (n 65507) 5,
   needLe (h 61) (n 20) 5, needLt (h 62) (n 16384000000) 5,
   needLe (h 3) (n ((2^64-1)/16000)) 5,
   needLe (h 4) (n ((2^64-1)/25600)) 5,
   needLe (h 5) (n ((2^64-1)/1600)) 5,
   saveMulDiv .x13 0 (h 3) (h 4) (n 1),
   needLe (.mem .x13 0) (n ((2^64-1)/500)) 5,
   checkedAdd .x13 0 (mul (.mem .x13 0) (n 500)) (n 200000),
   checkedAdd .x13 0 (.mem .x13 0) (mul layoutWords (n 100)),
   needLe (.mem .x13 0) (h 11) 5,
   needEq (mul layoutWords (n 8)) (.mem .x10 1) 5, O 0 (n 0)])

def init : SAsm.Stmt := sequence [
  needEq (h 0) (n 0) 10, nonzero (e 1) 2, flag (e 4),
  block [.LD .x14 .x10 48, .LD .x15 .x10 8], wipe .x14 .x15,
  H 0 (n 0x5245434f5631), H 1 (e 1), H 2 (e 3),
  H 3 (e 5), H 4 (e 6), H 5 (e 7), H 6 (e 8), H 7 (e 9), H 8 (e 10),
  H 9 (e 11), H 10 (e 12), H 11 (e 13), H 13 (n 1), H 31 (n 1), H 16 (e 2), H 17 (e 4),
  H 61 (e 14), H 62 (e 15), configCheck, pathAt (n 0), pathInit (n 1) (h 10)]

def headerCheck : SAsm.Stmt := sequence [needEq (h 0) (n 0x5245434f5631) 10,
  nonzero (h 1) 10, configCheck, nonzero (h 13) 10,
  needLe (h 12) (h 3) 10, needLe (h 14) (h 6) 10, needLe (h 15) (h 7) 10,
  needLe (h 14) (h 15) 10, needLe (h 15) (h 12) 10, needLt (h 21) (h 4) 10,
  needLe (h 22) (n 63) 10, needLe (h 31) (n 7) 10, needLe (h 23) (n 4) 10,
  needLt (h 24) (n 3) 10, needLe (h 27) (h 5) 10,
  needLe (h 28) (h 12) 10, needLe (h 59) (h 27) 10,
  needLt (h 30) (n (2^62)) 10,
  sequence ([17,18,19,20,29,57,58].map fun w => needLe (h w) (n 1) 10),
  needLe (h 19) (h 18) 10]

def spaceCheck : SAsm.Stmt := sequence <| (List.range 3).flatMap fun i =>
  [spaceAt (n i), needLe (z 0) (n (2^62)) 10, needLe (z 1) (n 1) 10,
   needLe (z 2) (z 0) 10, needLe (z 6) (z 0) 10,
   needLe (z 4) (h 15) 10, needLe (z 5) (h 12) 10]

/-- Raw provenance: init plus exclusive recovery ownership. This validator checks
all locally used record domains, references and aggregate accounting, including
path sums. It does not claim a hostile host cannot forge an entire valid history. -/
def recordCheck : SAsm.Stmt := sequence [set .x17 (n 0),
  block [.LD .x31 .x11 96],
  .loop (.ltu .x17 .x31) (sequence [packetAt (.reg .x17),
    needLe (n 1) (p 0) 10, needLe (p 0) (n 8) 10,
    needLt (p 1) (n 3) 10, needLt (p 2) (h 4) 10,
    spaceAt (p 1), needLt (p 3) (z 0) 10,
    nonzero (p 4) 10, needLe (p 4) (h 10) 10,
    sequence ([5,6,16,18,19].map fun w => needLe (p w) (n 1) 10),
    needLe (p 6) (p 5) 10, nonzero (p 11) 10, needLt (p 11) (h 13) 10,
    nonzero (p 12) 10, needLe (p 12) (h 8) 10, needLt (p 13) (p 14) 10, needLe (p 13) (p 17) 10, needLt (p 17) (p 14) 10,
    ne (p 16) (n 0) (sequence [needLe (p 17) (p 15) 10, needLe (p 15) (h 16) 10]),
    set .x17 (add (.reg .x17) (n 1)), block [.LD .x31 .x11 96]])]

end Libp2pAsm.Asm.Quic.Recovery
