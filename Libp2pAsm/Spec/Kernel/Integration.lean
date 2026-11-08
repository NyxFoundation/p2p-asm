import Libp2pAsm.Spec.Kernel.Registry
import Libp2pAsm.Spec.Kernel.Requests

namespace Libp2pAsm.Spec.Kernel

def replaceWords (a : List Nat) (offset : Nat) (xs : List Nat) : List Nat :=
  a.take offset ++ xs ++ a.drop (offset+xs.length)

def subWords (a : List Nat) (index : Nat) : List Nat :=
  (a.drop (a[index]!/8)).take ((a[index+1]!-a[index]!)/8)

def owned (state : List Nat) (input : List UInt8) (reap : Bool) : Result × List UInt8 := Id.run do
  if state[0]! != 2 then return (fail state 14,[])
  let req := subWords state 9
  let reg := subWords state 8
  let words := unpack input.toArray
  let send := !reap && words[2]! == 0
  let borrowed := if send then registry reg [words[9]!,words[10]!] 5 else ⟨0,0,0,reg⟩
  if borrowed.status != 0 then return (fail state borrowed.status,[])
  let (result,out) := requests req input (if reap then 2 else 0) 0
  if result.status != 0 then return (fail state result.status,[])
  let row := unpack out.toArray
  let reg := if reap && row[3]! == 0 then (registry reg [row[9]!,row[10]!] 6).state else borrowed.state
  let state := replaceWords (replaceWords state (state[8]!/8) reg) (state[9]!/8) result.state
  return ({result with state := state},out)

def resolveRegistered (state input : List Nat) (write : Nat) : Result := Id.run do
  let a := state.toArray
  if write > 1 then return fail state 4
  let rs := (List.range a[0]!).map fun i =>
    let s := slotAt a i
    (⟨s.generation,s.base,s.capacity,s.active,s.flags == 3⟩ : Abi.RegisteredRegion)
  let ref : Abi.BufferRef := ⟨input[0]!,input[1]!,input[2]!,input[3]!⟩
  match Abi.resolveBuffer rs.toArray ref (write == 1) with
  | .error e => return fail state e.code
  | .ok span =>
    let s := slotAt a ref.slot
    if (if write == 1 then s.writeBorrow != 1 else s.inputBorrow+s.sendBorrow == 0) then return fail state 15
    return ⟨0,span.address,span.length,state⟩

def kernelQuantum (state : List Nat) : Result := Id.run do
  let mut a := state.toArray
  if a[0]! != 2 then return fail state 14
  let r := a[8]!/8
  if a[r+2]! != 0 || a[r+15]! != 0 then return fail state 15
  a := (a.set! (a[9]!/8+14) 0).set! (a[10]!/8+7) 0
  let l := a[11]!/8
  let slot := a[l+10]!
  let lane := a[22]!
  if lane == 2 then a := a.set! (l+10) ((slot+1)%a[l]!)
  a := ((a.set! (l+3) 0).set! (l+9) 0).set! 22 ((lane+1)%5)
  return ⟨0,slot,lane,a.toList⟩

end Libp2pAsm.Spec.Kernel
