import Libp2pAsm.Asm.Quic.Recovery.Context

namespace Libp2pAsm.Asm.Quic.Recovery
open Rv64 Crypto.Util

def weighted (base : Reg) (w k : Nat) (a b : E) : SAsm.Stmt :=
  put base w (add (add (mul (div a (n (k+1))) (n k)) (div b (n (k+1))))
    (div (add (mul (.band a (n k)) (n k)) (.band b (n k))) (n (k+1))))

/-- Batch sampleTime is a ledger INDEX, despite its historical field name. -/
def rtt : SAsm.Stmt := sequence [packetAt (h 56), pathAt (p 2),
  needLe (p 15) (h 25) 2, Q 12 (sub (h 25) (p 15)), set .x17 (q 16),
  eq (.reg .x17) (n 0) (sequence [Q 13 (q 12), Q 14 (q 12),
    Q 15 (div (q 12) (n 2)), Q 16 (n 1), Q 17 (h 25)]),
  ne (.reg .x17) (n 0) (sequence [checkedAdd .x15 16 (q 16) (n 1),
    minimum .x15 13 (q 13) (q 12), O 0 (n 0),
    eq (h 19) (n 1) (eq (h 24) (n 2) (sequence [
      block [.LD .x5 .x11 488, .ADDI .x6 .x0 1, .SLL .x5 .x6 .x5,
        .ADDI .x6 .x0 1000, .MUL .x5 .x5 .x6, .SD .x13 .x5 0],
      block [.LD .x6 .x11 496, .DIVU .x6 .x6 .x5, .LD .x7 .x11 208],
      .ite (.ltu .x6 .x7) (O 0 (h 62)) (O 0 (mul (.mem .x13 0) (h 26)))])),
    O 1 (q 12), le (.mem .x13 0) (sub (q 12) (q 13))
      (O 1 (sub (q 12) (.mem .x13 0))),
    maximum .x13 2 (q 14) (.mem .x13 1), minimum .x13 3 (q 14) (.mem .x13 1),
    O 2 (sub (.mem .x13 2) (.mem .x13 3)),
    weighted .x15 15 3 (q 15) (.mem .x13 2), weighted .x15 14 7 (q 14) (.mem .x13 1)]),
  sequence ((List.range 4).map fun w => O w (n 0))]

def ackCC : SAsm.Stmt := eq (p 5) (n 1) (eq (p 0) (n 3) (sequence [
  Q 6 (sub (q 6) (p 4)), O 0 (n 0),
  eq (q 11) (n 1) (le (p 15) (q 10) (O 0 (n 1))),
  eq (p 18) (n 1) (O 0 (n 1)),
  eq (.mem .x13 0) (n 0) (sequence [
    block ((q 8).emit ++ (q 9).emit 1),
    .ite (.ltu .x5 .x6) (O 0 (p 4)) (saveMulDiv .x13 0 (q 24) (p 4) (q 8)),
    checkedAdd .x15 8 (q 8) (.mem .x13 0)])]))

def lossCC : SAsm.Stmt := eq (p 5) (n 1) (sequence [
  Q 6 (sub (q 6) (p 4)), O 0 (n 0),
  eq (q 11) (n 1) (le (p 15) (q 10) (O 0 (n 1))),
  eq (.mem .x13 0) (n 0) (sequence [
    maximum .x15 8 (mul (q 24) (n 2)) (div (q 8) (n 2)),
    Q 9 (q 8), Q 10 (h 25), Q 11 (n 1)])])

/-- Produces checked unbacked PTO in staged word 0. -/
def basePto (application : E) : SAsm.Stmt := sequence [
  needLe (q 15) (n ((2^64-1)/4)) 3,
  maximum .x13 0 (mul (q 15) (n 4)) (n 1000000),
  checkedAdd .x13 0 (.mem .x13 0) (q 14),
  eq application (n 2) (eq (h 19) (n 1) (checkedAdd .x13 0 (.mem .x13 0) (h 62)))]

def backoff : SAsm.Stmt := sequence [
  block [.LD .x5 .x11 176, .ADDI .x6 .x0 1, .SLL .x6 .x6 .x5, .SD .x13 .x6 48],
  saveMulDiv .x13 0 (.mem .x13 0) (.mem .x13 6) (n 1), O 6 (n 0)]

def timerSpace (i : Nat) : SAsm.Stmt := sequence [spaceAt (n i),
  eq (.band (.shr (h 31) (n i)) (n 1)) (n 1) (eq (z 1) (n 0) (ne (z 4) (n 0) (sequence [
    O 7 (h 21), set .x17 (n 0), block [.LD .x31 .x11 96],
    .loop (.ltu .x17 .x31) (sequence [packetAt (.reg .x17),
      eq (p 16) (n 1) (eq (p 6) (n 1) (eq (p 1) (n i)
        (eq (p 15) (z 3) (O 7 (p 2))))),
      set .x17 (add (.reg .x17) (n 1)), block [.LD .x31 .x11 96]]),
    pathAt (.mem .x13 7), O 2 (n 0), ampTest (n 1200) (O 2 (n 1)),
    eq (.mem .x13 2) (n 0) (sequence [
      basePto (n i), backoff, checkedAdd .x13 0 (.mem .x13 0) (z 3),
      eq (.mem .x13 4) (n 0) (sequence [O 4 (.mem .x13 0), O 1 (n i), O 5 (.mem .x13 7)]),
      lt (.mem .x13 0) (.mem .x13 4) (sequence [O 4 (.mem .x13 0), O 1 (n i), O 5 (.mem .x13 7)])])])))]

def timer : SAsm.Stmt := sequence [ready,
  sequence ((List.range 3).map fun i => sequence [spaceAt (n i),
    eq (z 1) (n 0) (ne (z 7) (n 0) (sequence [
      eq (.mem .x13 4) (n 0) (sequence [O 4 (z 7), O 1 (n i)]),
      lt (z 7) (.mem .x13 4) (sequence [O 4 (z 7), O 1 (n i)])]))]),
  ne (.mem .x13 4) (n 0) (sequence [O 0 (n 11), O 3 (n 1)]),
  eq (.mem .x13 4) (n 0) (sequence [selectPath (h 21),
    O 7 (n 0),
    eq (.mem .x13 7) (n 0) (sequence [timerSpace 0, timerSpace 1,
      eq (h 19) (n 1) (timerSpace 2),
      eq (.mem .x13 4) (n 0) (eq (h 17) (n 0) (eq (h 20) (n 0) (sequence [
        pathAt (h 21), O 5 (h 21), spaceAt (n 1), O 1 (n 1), O 7 (z 1),
        eq (.band (h 31) (n 2)) (n 0) (O 7 (n 1)), ne (.mem .x13 7) (n 0) (sequence [spaceAt (n 0), O 1 (n 0)]),
        eq (z 1) (n 0) (sequence [needEq (.band (.shr (h 31) (.mem .x13 1)) (n 1)) (n 1) 10, basePto (.mem .x13 1), backoff,
          checkedAdd .x13 4 (q 25) (.mem .x13 0)])]))),
      ne (.mem .x13 4) (n 0) (sequence [O 0 (n 11), O 3 (n 2)])]),
    O 2 (n 0), O 7 (n 0), eq (.mem .x13 4) (n 0) (O 0 (n 0))])]

end Libp2pAsm.Asm.Quic.Recovery
