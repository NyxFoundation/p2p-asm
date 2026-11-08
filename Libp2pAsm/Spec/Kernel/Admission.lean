import Libp2pAsm.Spec.Kernel.Words

namespace Libp2pAsm.Spec.Kernel

structure Window where
  epoch : Nat
  datagrams : Nat
  bytes : Nat
  previousDatagrams : Nat
  previousBytes : Nat
  deriving Repr, BEq

/-- Conservative two-bucket admission: counts the entire preceding bucket, so an
accepted rolling interval cannot exceed policy even at a bucket boundary. -/
def Window.rotate (w : Window) (now width : Nat) : Window :=
  if now-w.epoch < width then w else
  { epoch := now-now%width,datagrams := 0,bytes := 0,
    previousDatagrams := if (now-w.epoch)/width == 1 then w.datagrams else 0,
    previousBytes := if (now-w.epoch)/width == 1 then w.bytes else 0 }

def Window.allowed (w : Window) (length datagrams bytes : Nat) : Bool :=
  w.datagrams+w.previousDatagrams < datagrams && w.bytes+w.previousBytes+length ≤ bytes

def Window.count (w : Window) (length : Nat) : Window :=
  {w with datagrams := min wordMax (w.datagrams+1),bytes := min wordMax (w.bytes+length)}

def windowAt (a : Array Nat) (i : Nat) : Window := ⟨a[i]!,a[i+1]!,a[i+2]!,a[i+3]!,a[i+4]!⟩
def setWindow (a : Array Nat) (i : Nat) (w : Window) : Array Nat :=
  [w.epoch,w.datagrams,w.bytes,w.previousDatagrams,w.previousBytes].zipIdx.foldl
    (fun a (n,j) => a.set! (i+j) n) a

def admission (state input : List Nat) : Result := Id.run do
  let mut a := state.toArray
  let source := input[0]!
  let now := input[1]!
  let length := input[2]!
  if source ≥ a[0]! then return fail state 13
  let d := 32+16*source
  if now < a[6]! || now < a[d+5]! then return fail state 24
  let global := (windowAt a 1).rotate now a[10]!
  let sourceWindow :=  (windowAt a d).rotate now a[10]!
  let reason := if !(global.allowed length a[8]! a[9]! && sourceWindow.allowed length a[25]! a[26]!) then 1 else 0
  let reason := if a[7]! ≥ a[11]! then 2 else reason
  let reason := if length > a[28]! then 3 else reason
  let reason := if input[3]! != 0 then 4 else reason
  a := setWindow (setWindow a 1 (global.count length)) d (sourceWindow.count length)
  a := ((a.set! 6 now).set! (d+5) now).set! 7 (min wordMax (a[7]!+1))
  if reason != 0 then a := (a.set! 12 (min wordMax (a[12]!+1))).set! (d+11) (min wordMax (a[d+11]!+1))
  return ⟨0,(if reason == 0 then 0 else 1),reason,a.toList⟩

structure Charge where
  quantum : Nat
  connection : Nat
  global : Nat
  deriving Repr, BEq

def Charge.tryCharge (s limits : Charge) (cost : Nat) : Except Nat Charge :=
  if 0 < cost ∧ s.quantum+cost ≤ limits.quantum ∧ s.connection+cost ≤ limits.connection ∧ s.global+cost ≤ limits.global then
    .ok ⟨s.quantum+cost,s.connection+cost,s.global+cost⟩ else .error 19

def charge (state input : List Nat) : Result := Id.run do
  let a := state.toArray
  let slot := input[0]!
  if slot ≥ a[0]! then return fail state 13
  let d := 16+8*slot
  if a[d]! != input[1]! || a[d+1]! == 0 || a[d+1]! ≥ 3 then return fail state 14
  let now := input[2]!
  if now < a[1]! || now < a[d+3]! then return fail state 24
  let global := if now-a[1]! ≥ a[4]! then 0 else a[2]!
  let connection := if now-a[d+3]! ≥ a[4]! then 0 else a[d+4]!
  let cost := input[3]!
  let actions := input[4]!
  match (Charge.mk a[3]! connection global).tryCharge ⟨a[5]!,a[6]!,a[7]!⟩ cost with
  | .error e => return fail state e
  | .ok next =>
    if a[9]!+actions > a[8]! then return fail state 19
    let a := (((a.set! 2 next.global).set! (d+4) next.connection).set! 3 next.quantum).set! 9 (a[9]!+actions)
    let a := if now-a[1]! ≥ a[4]! then a.set! 1 now else a
    let a := if now-a[d+3]! ≥ a[4]! then a.set! (d+3) now else a
    return ⟨0,cost,actions,a.toList⟩

def nextQuantum (state : List Nat) : Result :=
  let a := state.toArray
  let slot := a[10]!
  let a := ((a.set! 10 ((slot+1)%a[0]!)).set! 3 0).set! 9 0
  ⟨0,slot,a[16+8*slot+1]!,a.toList⟩

end Libp2pAsm.Spec.Kernel
