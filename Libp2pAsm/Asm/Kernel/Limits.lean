import Libp2pAsm.Asm.Kernel.Common

namespace Libp2pAsm.Asm.Kernel
open Rv64

/-- Compile-time expression tree; lowered exclusively to loads and RV64IM arithmetic. -/
inductive Amount where
  | field (index : Nat) | literal (value : Nat)
  | add (a b : Amount) | mul (a b : Amount)
  | align (a : Amount) (multiple : Nat)
  deriving Inhabited
open Amount

def amount (e : Amount) (err : Nat) (depth : Nat := 0) : SAsm.Stmt :=
  match e with
  | .field n => input .x24 n
  | .literal n => li .x24 n
  | .align a n => seq [amount a err depth,li .x25 (n-1),
    addChecked .x24 .x24 .x25 err,ins [.ANDI .x24 .x24 (BitVec.ofInt 12 (-Int.ofNat n))]]
  | .add a b | .mul a b => seq [amount a err (depth+1),
    ins [.SD .x2 .x24 (imm (128+depth*8))],amount b err (depth+1),
    ins [.LD .x25 .x2 (imm (128+depth*8))],
    match e with
    | .mul .. => mulChecked .x24 .x25 .x24 err
    | _ => addChecked .x24 .x25 .x24 err]

def leField (a b err : Nat) : SAsm.Stmt := seq [input .x24 a,input .x25 b,reject (.ltu .x25 .x24) err]
def lowerBound (n field err : Nat) : SAsm.Stmt := seq [li .x24 n,input .x25 field,reject (.ltu .x25 .x24) err]
def upperBound (field n err : Nat) : SAsm.Stmt := seq [li .x24 n,input .x25 field,reject (.ltu .x24 .x25) err]
def equalField (field n err : Nat) : SAsm.Stmt := seq [li .x24 n,input .x25 field,reject (.ne .x24 .x25) err]
def fitField (e : Amount) (field err : Nat) : SAsm.Stmt := seq [amount e err,input .x25 field,reject (.ltu .x25 .x24) err]

def requiredCompletions : Amount := .add (.add (.field 31) (.field 30)) (.add (.field 32) (.field 33))
def requiredTimers : Amount :=
  .add (.add (.add (.mul (.literal 5) (.field 0)) (.field 2)) (.mul (.field 0) (.field 16)))
    (.add (.field 30) (.add (.field 32) (.field 33)))

def reservation : Amount :=
  .add (.add (.mul (.field 0)
    (.add (.add (.add (.field 56) (.field 57)) (.mul (.literal 2) (.field 19)))
      (.mul (.field 16) (.add (.field 17) (.field 18)))))
    (.mul (.add (.field 15) (.field 30)) (.field 10)))
    (.add (.mul (.field 27) (.literal 256)) (.add (.field 58) (.field 59)))

/-- Exactly frozen Limits.validate priority. x24 receives reservedBytes. -/
def validateLimitsBody : SAsm.Stmt := seq [
  li .x7 488,reject (.ne .x19 .x7) 1,
  mov .x26 .x18,li .x27 61,
  .loop (.ne .x27 .x0) (seq [readLE .x24 .x26 0,reject (.eq .x24 .x0) 1,
    ins [.ADDI .x26 .x26 8,.ADDI .x27 .x27 (-1)]]),
  seq ([(1,0),(2,0),(3,2),(3,1),(0,4),(6,5)].map fun (a,b) => leField a b 2),
  lowerBound 2 24 2,lowerBound 2 23 2,
  lowerBound 1200 10 3,upperBound 10 65507 3,leField 11 13 3,leField 11 15 3,
  leField 10 14 3,fitField (.mul (.literal 2) (.field 20)) 21 3,
  equalField 47 2 4,equalField 48 1 4,fitField (.add (.field 47) (.field 48)) 16 4,
  leField 45 17 4,leField 45 18 4,lowerBound 4096 49 4,leField 49 19 4,leField 50 49 4,
  fitField requiredCompletions 28 5,fitField (.add (.add (.field 28) (.field 15)) (.field 29)) 27 5,
  fitField requiredTimers 31 5,leField 37 36 6,leField 51 52 7,leField 52 53 7,
  input .x24 59,ins [.ANDI .x24 .x24 15],reject (.ne .x24 .x0) 8,
  fitField reservation 55 8]

def validateLimits : SAsm.Stmt := seq [enter 0 0 0,validateLimitsBody,success .x24 .x0]

/-- Raw export preserves the exact original Limits byte layout; no struct padding. -/
def exportLimits : SAsm.Stmt := seq [enter 0 0 488,validateLimitsBody,
  mov .x26 .x18,mov .x27 .x20,li .x29 488,
  .loop (.ne .x29 .x0) (ins [.LBU .x5 .x26 0,.SB .x27 .x5 0,
    .ADDI .x26 .x26 1,.ADDI .x27 .x27 1,.ADDI .x29 .x29 (-1)]),
  li .x24 488,success .x24 .x0]

end Libp2pAsm.Asm.Kernel
