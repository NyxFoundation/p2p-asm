import Libp2pAsm.Spec.Kernel.Words

namespace Libp2pAsm.Spec.Kernel

structure Reservation where
  capacity : Nat
  queued : Nat
  reserved : Nat
  deriving Repr, BEq

def Reservation.valid (r : Reservation) : Prop := r.queued+r.reserved ≤ r.capacity

def Reservation.reserve (r : Reservation) : Except Nat Reservation :=
  if r.queued+r.reserved < r.capacity then .ok {r with reserved := r.reserved+1} else .error 19

def Reservation.deliver (r : Reservation) : Except Nat Reservation :=
  if 0 < r.reserved then .ok {r with queued := r.queued+1,reserved := r.reserved-1} else .error 14

def queue (state : List Nat) (bytes : List UInt8) (op source : Nat) : Result × List UInt8 := Id.run do
  let a := state.toArray
  let cap := a[0]!
  let head := a[1]!
  let count := a[2]!
  let reserved := a[3]!
  let bad := fun e => (fail state e,[])
  if op == 2 then
    if count+reserved ≥ cap then return bad 19
    return (⟨0,0,0,(a.set! 3 (reserved+1)).toList⟩,[])
  if op == 3 then
    if reserved == 0 then return bad 14
    return (⟨0,0,0,(a.set! 3 (reserved-1)).toList⟩,[])
  if op == 1 then
    if count == 0 then return bad 19
    let off := a[5]!/8+32*head
    let record := (a.extract off (off+32)).toList
    let a := (List.range 32).foldl (fun a i => a.set! (off+i) 0) a
    let a := (a.set! 1 ((head+1)%cap)).set! 2 (count-1)
    return (⟨0,record[0]!,record[1]!,a.toList⟩,pack record)
  unless source == a[4]! && source ≤ 4 do return bad 23
  if bytes.length > 224 then return bad 13
  if op == 4 then
    if source != 2 then return bad 23
    if reserved == 0 then return bad 14
  else if count+reserved ≥ cap then return bad (if source == 0 then 20 else 19)
  let off := a[5]!/8+32*((head+count)%cap)
  let body := unpack (bytes ++ List.replicate (224-bytes.length) 0).toArray
  let words := [source,bytes.length,0,0] ++ body
  let a := (words.zipIdx.foldl (fun a (n,i) => a.set! (off+i) n) a).set! 2 (count+1)
  let a := if op == 4 then a.set! 3 (reserved-1) else a
  return (⟨0,0,0,a.toList⟩,[])

end Libp2pAsm.Spec.Kernel
