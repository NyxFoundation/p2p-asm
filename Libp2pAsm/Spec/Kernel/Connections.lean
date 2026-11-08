import Libp2pAsm.Spec.Kernel.Words

namespace Libp2pAsm.Spec.Kernel

def starts (a : Array Nat) (i now width : Nat) : List Nat :=
  if now-a[i]! < width then [a[i]!,a[i+1]!,a[i+2]!] else
    [now-now%width,0,if (now-a[i]!)/width == 1 then a[i+1]! else 0]

def connections (state v : List Nat) (op : Nat) : Result := Id.run do
  let mut a := state.toArray
  if op == 0 && a[20]! != 0 then return fail state 15
  if a[0]! != 2 then return fail state 14
  let g := a[10]!/8
  let l := a[11]!/8
  if v[0]! ≥ a[l]! then return fail state 13
  let d := l+16+8*v[0]!
  if a[d]! != v[1]! then return fail state 14
  let phase := a[d+1]!
  if op == 0 then
    if phase == 3 then return fail state 16
    if phase != 0 then return fail state 15
  else if phase == 0 || phase ≥ 3 then return fail state 14
  let source := if op == 0 then v[2]! else a[d+2]!
  if source ≥ a[g]! then return fail state 13
  let p := g+32+16*source
  if op == 0 then
    let now := v[3]!
    if now < a[g+6]! then return fail state 24
    if a[g+22]! ≥ a[g+23]! || a[p+10]! ≥ a[g+24]! || a[g+21]! ≥ a[g+16]! || a[p+9]! ≥ a[g+17]! then return fail state 19
    if now < a[g+13]! || now < a[p+6]! then return fail state 24
    let global := starts a (g+13) now a[g+20]!
    let sourceStarts := starts a (p+6) now a[g+20]!
    if global[1]!+global[2]! ≥ a[g+18]! || sourceStarts[1]!+sourceStarts[2]! ≥ a[g+19]! then return fail state 19
    for (i,xs) in [(g+13,global),(p+6,sourceStarts)] do
      a := ((a.set! i xs[0]!).set! (i+1) (xs[1]!+1)).set! (i+2) xs[2]!
    for i in [g+22,p+10,g+21,p+9] do a := a.set! i (a[i]!+1)
    a := [1,source,now,0,0,0,0].zipIdx.foldl (fun a (n,i) => a.set! (d+1+i) n) a
    return ⟨0,v[0]!,v[1]!,a.toList⟩
  if op == 1 && phase != 1 then return fail state 14
  if phase == 1 then
    a := (a.set! (g+21) (a[g+21]!-1)).set! (p+9) (a[p+9]!-1)
  if op == 1 then return ⟨0,0,0,(a.set! (d+1) 2).toList⟩
  a := (a.set! (g+22) (a[g+22]!-1)).set! (p+10) (a[p+10]!-1)
  a := if a[d]! == wordMax then a.set! (d+1) 3 else (a.set! d (a[d]!+1)).set! (d+1) 0
  a := (List.range 6).foldl (fun a i => a.set! (d+2+i) 0) a
  return ⟨0,0,0,a.toList⟩

def connectionCleanup (state : List Nat) (mode : Nat) : Result × List UInt8 := Id.run do
  let mut a := state.toArray
  if a[0]! != 2 then return (fail state 14,[])
  if a[20]! == 0 then
    if mode != 1 && mode != 2 then return (fail state 12,[])
    a := (a.set! 20 mode).set! 21 0
  let l := a[11]!/8
  let slot := a[21]!
  if slot ≥ a[l]! then return (⟨0,0,0,((a.set! 20 0).set! 21 0).toList⟩,[])
  a := a.set! 21 (slot+1)
  let d := l+16+slot*8
  let phase := a[d+1]!
  if phase == 0 || phase ≥ 3 || (a[20]! == 1 && phase != 1) then
    return (⟨0,1,slot,a.toList⟩,[])
  let out := pack [slot,a[d]!,a[d+2]!,phase]
  let r := connections a.toList [slot,a[d]!] 2
  return ({r with first := 2,second := slot},out)

end Libp2pAsm.Spec.Kernel
