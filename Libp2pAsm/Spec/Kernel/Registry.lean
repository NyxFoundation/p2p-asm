import Libp2pAsm.Spec.Kernel.Words
import Libp2pAsm.Spec.Abi.Buffer

namespace Libp2pAsm.Spec.Kernel

structure Slot where
  generation : Nat := 0
  base : Nat := 0
  capacity : Nat := 0
  flags : Nat := 0
  inputBorrow : Nat := 0
  sendBorrow : Nat := 0
  writeBorrow : Nat := 0
  retired : Nat := 0
  deriving Repr, BEq

def Slot.active (s : Slot) : Bool := s.flags % 2 == 1

def Slot.borrowed (s : Slot) : Bool := s.inputBorrow+s.sendBorrow+s.writeBorrow != 0

def Slot.release (s : Slot) : Slot :=
  {generation := min wordMax (s.generation+1),retired := if s.generation == wordMax then 1 else 0}

def Slot.acquire (s : Slot) (kind : Nat) : Except Nat Slot := do
  unless s.active do throw 14
  if kind == 0 then
    unless s.inputBorrow == 0 && s.writeBorrow == 0 do throw 15
    return {s with inputBorrow := 1}
  if kind == 1 then
    unless s.sendBorrow == 0 && s.writeBorrow == 0 do throw 15
    return {s with sendBorrow := 1}
  unless kind == 2 do throw 12
  unless s.flags == 3 do throw 21
  unless !s.borrowed do throw 15
  return {s with writeBorrow := 1}

def Slot.endBorrow (s : Slot) (kind : Nat) : Except Nat Slot := do
  if kind == 0 then
    unless s.inputBorrow == 1 do throw 14
    return {s with inputBorrow := 0}
  if kind == 1 then
    unless s.sendBorrow == 1 do throw 14
    return {s with sendBorrow := 0}
  unless kind == 2 do throw 12
  unless s.writeBorrow == 1 do throw 14
  return {s with writeBorrow := 0}

def slotAt (a : Array Nat) (i : Nat) : Slot :=
  let d := 16+4*i
  let m := 16+4*a[0]!+4*i
  ⟨a[d]!,a[d+1]!,a[d+2]!,a[d+3]!,a[m]!,a[m+1]!,a[m+2]!,a[m+3]!⟩

def setSlot (a : Array Nat) (i : Nat) (s : Slot) : Array Nat :=
  let d := 16+4*i
  let m := 16+4*a[0]!+4*i
  let pairs := [(d,s.generation),(d+1,s.base),(d+2,s.capacity),(d+3,s.flags),
    (m,s.inputBorrow),(m+1,s.sendBorrow),(m+2,s.writeBorrow),(m+3,s.retired)]
  pairs.foldl (fun a (i,n) => a.set! i n) a

def registryBegin (a : Array Nat) (v : List Nat) : Except Nat (Array Nat) := do
  unless a[8]! == 0 && a[15]! == 0 do throw 15
  let i := v[0]!
  unless i < a[0]! do throw 13
  let s := slotAt a i
  unless s.generation == v[1]! do throw 14
  unless !s.active && !s.borrowed do throw 15
  unless s.retired == 0 do throw 16
  unless v[4]! ≤ 1 && v[3]! > 0 && v[2]!+v[3]! ≤ wordMax do throw 9
  unless disjoint v[2]! v[3]! a[4]! a[5]! ∧ disjoint v[2]! v[3]! a[6]! a[7]! do throw 18
  return (((((((a.set! 8 1).set! 9 i).set! 10 v[2]!).set! 11 v[3]!).set! 12 v[4]!).set! 13 0).set! 14 v[1]!)

/-- A registration scan owns its cursor; no descriptor becomes live until all slots pass. -/
def registryScan (a : Array Nat) : Array Nat × Nat × Nat := Id.run do
  let mut a := a
  let stop := min a[0]! (a[13]!+32)
  for i in [a[13]!:stop] do
    let s := slotAt a i
    if s.active && (s.flags == 3 || a[12]! == 1) &&
        !(decide (disjoint a[10]! a[11]! s.base s.capacity)) then
      a := (List.range 7).foldl (fun a i => a.set! (8+i) 0) a
      return (a,2,18)
  a := a.set! 13 stop
  if stop < a[0]! then return (a,1,stop)
  let s : Slot := ⟨a[14]!,a[10]!,a[11]!,1+2*a[12]!,0,0,0,0⟩
  a := (setSlot a a[9]! s).set! 1 (a[1]!+1)
  a := (List.range 7).foldl (fun a i => a.set! (8+i) 0) a
  return (a,0,0)

def registry (state input : List Nat) (op : Nat) : Result := Id.run do
  let a := state.toArray
  if op == 0 then
    match registryBegin a input with
    | .error e => return fail state e
    | .ok a => return ⟨0,1,0,a.toList⟩
  if op == 1 then
    if a[8]! != 1 then return fail state 14
    let (a,x,y) := registryScan a
    return ⟨0,x,y,a.toList⟩
  if op == 9 then
    let start := a[15]!-1
    let stop := min a[0]! (start+32)
    let a := (List.range (stop-start)).foldl (fun a j =>
      let i := 16+4*a[0]!+4*(start+j)
      if a[i]! == 0 then a else (a.set! i 0).set! 2 (a[2]!-1)) a
    let a := a.set! 15 (if stop < a[0]! then stop+1 else 0)
    return ⟨0,(if stop < a[0]! then 1 else 0),stop,a.toList⟩
  if op > 8 then return fail state 12
  if (a[8]! != 0 || a[15]! != 0) && op != 4 && op != 6 && op != 8 then return fail state 15
  let i := input[0]!
  if i ≥ a[0]! then return fail state 13
  let s := slotAt a i
  if s.generation != input[1]! || !s.active then return fail state 14
  if op == 2 then
    if s.borrowed then return fail state 15
    return ⟨0,0,0,((setSlot a i s.release).set! 1 (a[1]!-1)).toList⟩
  let kind := (op-3)/2
  let acquiring := op%2 == 1
  let result := if acquiring then s.acquire kind else s.endBorrow kind
  match result with
  | .error e => return fail state e
  | .ok s =>
    let a := setSlot a i s
    let a := if kind < 2 then a.set! (2+kind) (if acquiring then a[2+kind]!+1 else a[2+kind]!-1) else a
    return ⟨0,0,0,a.toList⟩

end Libp2pAsm.Spec.Kernel
