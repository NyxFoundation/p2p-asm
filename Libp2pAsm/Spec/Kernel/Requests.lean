import Libp2pAsm.Spec.Kernel.Words

namespace Libp2pAsm.Spec.Kernel

def requestOffset (slot : Nat) : Nat := 32+16*slot

def payloadOffset (a : Array Nat) (slot : Nat) : Nat := 32+16*a[0]!+slot*(a[12]!/8)

def wipeRequest (a : Array Nat) (slot : Nat) : Array Nat :=
  if a[requestOffset slot+3]! == 3 then a else
  (List.range (a[12]!/8)).foldl (fun a i => a.set! (payloadOffset a slot+i) 0) a

def requestIssue (a : Array Nat) (v : List Nat) : Except Nat (Array Nat × Nat × Nat × List UInt8) := do
  unless a[16]! == 0 do throw 15
  let slot := v[0]!
  unless slot < a[0]! do throw 13
  let d := requestOffset slot
  unless a[d]! == v[1]! do throw 14
  unless a[d+1]! != 4 do throw 16
  unless a[d+1]! == 0 do throw 15
  let kind := v[2]!
  unless kind ≤ 3 do throw 12
  unless (if kind == 3 then slot ≥ a[0]!-a[7]! else slot < a[0]!-a[7]!) do throw 13
  unless a[8+kind]! < a[4+kind]! && a[1]! < a[3]! && a[14]! < a[13]! do throw 19
  unless a[2]! != 0 do throw 17
  unless v[5]! ≤ a[12]! && (kind != 3 || v[5]! == 0) do throw 13
  unless v[8]! ≤ 1 do throw 12
  let delay := if kind == 3 then v[4]! else a[18+kind]!
  unless delay > 0 do throw 13
  let deadline := v[3]!+delay
  unless deadline ≤ wordMax do throw 17
  let id := a[2]!
  let record := [v[1]!,1,id,kind,deadline] ++ (v.drop 5).take 6 ++ [0,0,0,0,0]
  let a := record.zipIdx.foldl (fun a (n,i) => a.set! (d+i) n) a
  let a := (((a.set! 1 (a[1]!+1)).set! (8+kind) (a[8+kind]!+1)).set! 14 (a[14]!+1)).set! 2
    (if id == wordMax then 0 else id+1)
  return (a,id,deadline,pack record)

def matchRequest (a : Array Nat) (v : List Nat) (phase : Nat) : Except Nat Nat := do
  unless v[0]! < a[0]! do throw 13
  let d := requestOffset v[0]!
  unless a[d]! == v[1]! && a[d+1]! == phase do throw 14
  return d

def requestComplete (a : Array Nat) (v : List Nat) (body : List UInt8) (source : Nat) :
    Except Nat (Array Nat × Nat) := do
  unless source == 2 do throw 23
  let d ← matchRequest a v 1
  unless a[d+2]! == v[2]! && a[d+3]! == v[3]! do throw 14
  let now := v[4]!
  unless a[d+3]! != 3 || now ≥ a[d+4]! do throw 25
  unless v[5]! ≤ 3 do throw 12
  let result := if a[d+3]! != 3 && now ≥ a[d+4]! then 4 else v[5]!
  let result := if v[6]! != body.length || v[6]! != a[d+5]! then 6 else result
  let a := wipeRequest a v[0]!
  let a := if result == 0 && a[d+3]! != 3 then
    let padded := body ++ List.replicate (a[12]!-body.length) 0
    (unpack padded.toArray).zipIdx.foldl (fun a (n,i) => a.set! (payloadOffset a v[0]!+i) n) a
    else a
  return ((((a.set! (d+1) 2).set! (d+14) result).set! (d+15) now),result)

def requestReap (a : Array Nat) (v : List Nat) : Except Nat (Array Nat × Nat × Nat × List UInt8) := do
  let d ← matchRequest a v 2
  let kind := a[d+3]!
  let id := a[d+2]!
  let outcome := a[d+14]!
  let bytes := pack (a.extract d (d+16)).toList ++
    (if kind == 3 then [] else pack (a.extract (payloadOffset a v[0]!)
      (payloadOffset a v[0]!+a[12]!/8)).toList)
  let a := wipeRequest a v[0]!
  let a := (List.range 14).foldl (fun a i => a.set! (d+2+i) 0) a
  let a := if a[d]! == wordMax then a.set! (d+1) 4 else (a.set! d (a[d]!+1)).set! (d+1) 0
  let a := (a.set! 1 (a[1]!-1)).set! (8+kind) (a[8+kind]!-1)
  return (a,id,outcome,bytes)

def requestCleanup (a : Array Nat) (mode : Nat) : Except Nat (Array Nat × Nat × Nat) := do
  let a ← if a[16]! == 0 then do
    unless mode == 1 || mode == 2 do throw 12
    pure ((a.set! 16 mode).set! 17 0)
    else pure a
  let slot := a[17]!
  if slot ≥ a[0]! then return (((a.set! 16 0).set! 17 0),0,0)
  let d := requestOffset slot
  let a := if (a[d+1]! == 1 || a[d+1]! == 2) && (a[16]! == 2 || a[d+8]! != 0) then
    ((wipeRequest a slot).set! (d+1) 2).set! (d+14) 5 else a
  return (a.set! 17 (slot+1),1,slot+1)

def requestStop (a : Array Nat) (v : List Nat) (expiry : Bool) : Except Nat (Array Nat × Nat) := do
  let d ← matchRequest a v 1
  unless a[d+2]! == v[2]! do throw 14
  if expiry then unless v[3]! ≥ a[d+4]! do throw 25
  let outcome := if expiry then (if a[d+3]! == 3 then 0 else 4) else 5
  let a := ((wipeRequest a v[0]!).set! (d+1) 2).set! (d+14) outcome
  return (a,outcome)

def requests (state : List Nat) (input : List UInt8) (op source : Nat) : Result × List UInt8 :=
  let a := state.toArray
  let v := unpack input.toArray
  match op with
  | 0 => match requestIssue a v with
    | .error e => (fail state e,[])
    | .ok (a,x,y,out) => (⟨0,x,y,a.toList⟩,out)
  | 1 => match requestComplete a v (input.drop 56) source with
    | .error e => (fail state e,[])
    | .ok (a,x) => (⟨0,x,0,a.toList⟩,[])
  | 2 => match requestReap a v with
    | .error e => (fail state e,[])
    | .ok (a,x,y,out) => (⟨0,x,y,a.toList⟩,out)
  | 3 => match requestCleanup a source with
    | .error e => (fail state e,[])
    | .ok (a,x,y) => (⟨0,x,y,a.toList⟩,[])
  | 4 | 5 => match requestStop a v (op == 5) with
    | .error e => (fail state e,[])
    | .ok (a,x) => (⟨0,x,0,a.toList⟩,[])
  | 6 => Id.run do
    let mut a := a
    for _ in [:32] do
      let slot := a[22]!
      a := a.set! 22 ((slot+1)%a[0]!)
      if a[requestOffset slot+1]! == 2 then return (⟨0,slot+1,a[22]!,a.toList⟩,[])
    return (⟨0,0,a[22]!,a.toList⟩,[])
  | 7 => Id.run do
    let slot := a[23]!
    let d := requestOffset slot
    let a := a.set! 23 ((slot+1)%a[0]!)
    if a[d+1]! != 1 || v[0]! < a[d+4]! then return (⟨0,0,slot,a.toList⟩,[])
    let outcome := if a[d+3]! == 3 then 0 else 4
    let a := (((wipeRequest a slot).set! (d+1) 2).set! (d+14) outcome).set! (d+15) v[0]!
    return (⟨0,slot+1,outcome,a.toList⟩,[])
  | _ => (fail state 12,[])

end Libp2pAsm.Spec.Kernel
