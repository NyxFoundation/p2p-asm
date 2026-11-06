import Libp2pAsm.Spec.Kernel.Limits

namespace Libp2pAsm.Spec.Kernel

def align (n a : Nat) : Nat := ((n+a-1)/a)*a

def kernelAreas (l : Limits) : List Nat :=
  let req := l.maxPendingSends+l.maxEntropyRequests+l.maxClockRequests
  [128+64*l.maxRegions,256+128*(req+l.maxTimers)+align l.maxDatagramBytes 8*req,
   256+128*l.maxSources,128+64*l.maxConnections,64+256*l.maxContinuations,
   64+256*l.maxActions,192]

def kernelOffsets (l : Limits) : List Nat :=
  (kernelAreas l).foldl (fun xs n => xs ++ [xs.getLast!+n]) [1024]

def connectionBytes (l : Limits) : Nat := l.maxConnections *
  (l.connectionMetadataBytes+l.cryptoScratchBytes+2*l.cryptoBufferBytes+
    l.maxStreamsPerConnection*(l.streamReceiveBytes+l.streamSendBytes))

def layout (l : Limits) (allocated : Nat) : Except Nat (List Nat) := do
  l.validate.mapError limitsErrorCode
  let offs := kernelOffsets l
  unless offs.getLast! ≤ l.globalMetadataBytes do throw 22
  unless l.globalMetadataBytes % 16 == 0 do throw 22
  let data := l.globalMetadataBytes+connectionBytes l
  let events := align (data+(l.maxQueuedDatagrams+l.maxPendingSends)*l.maxDatagramBytes) 16
  let stack := events+l.maxInputEvents*256
  let used := stack+l.maxStackBytes
  unless used ≤ l.arenaBytes && used ≤ allocated && used ≤ wordMax do throw 22
  unless 1000000 ≤ l.maxInstructionsPerQuantum do throw 22
  return offs.take 7 ++ [l.globalMetadataBytes,data,events,stack,used]

def initBegin (state : List Nat) (bs : Array UInt8) (base allocated code codeBytes : Nat) : Result :=
  match validateRaw bs with
  | .error e => fail state e
  | .ok l => match layout l allocated with
    | .error e => fail state e
    | .ok offsets => Id.run do
      let mut a := state.toArray
      a := a.mapIdx fun i n => if i < 128 then 0 else n
      let metadata :=  (kernelOffsets l).getLast!
      let fields := [(0,1),(1,offsets[11]!),(2,1024),(3,metadata),(4,allocated),(5,code),(6,codeBytes)]
      a := fields.foldl (fun a (i,n) => a.set! i n) a
      a := offsets.zipIdx.foldl (fun a (n,i) => a.set! (8+i) n) a
      a := l.wordFields.zipIdx.foldl (fun a (n,i) => a.set! (64+i) n) a
      if base%16 != 0 then return fail state 10
      return ⟨0,1,1024,a.toList⟩

def initHeaders (a : Array Nat) (base : Nat) : Array Nat := Id.run do
  let v := a.extract 64 125
  let put := fun (a : Array Nat) (t : Nat) (xs : List (Nat × Nat)) =>
    xs.foldl (fun a (i,n) => a.set! (a[8+t]!/8+i) n) a
  let mut a := put a 0 [(0,v[60]!),(4,base),(5,a[1]!),(6,a[5]!),(7,a[6]!)]
  a := put a 1 [(0,v[30]!+v[31]!+v[32]!+v[33]!),(2,1),(3,v[28]!),
    (4,v[30]!),(5,v[32]!),(6,v[33]!),(7,v[31]!),(12,align v[10]! 8),
    (13,v[35]!),(18,v[38]!),(19,v[40]!),(20,v[41]!)]
  a := put a 2 [(0,v[4]!),(8,v[13]!),(9,v[14]!),(10,v[12]!),(11,v[11]!),
    (16,v[2]!),(17,v[3]!),(18,v[5]!),(19,v[6]!),(20,v[7]!),
    (23,v[0]!),(24,v[1]!),(28,v[10]!),(25,max 1 (v[13]!/v[4]!)),(26,max v[10]! (v[14]!/v[4]!))]
  a := put a 3 [(0,v[0]!),(4,v[54]!),(5,v[51]!),(6,v[52]!),(7,v[53]!),(8,v[35]!)]
  a := put a 4 [(0,v[34]!),(4,3),(5,64)]
  a := put a 5 [(0,v[35]!),(4,4),(5,64)]
  let mut q := a[14]!/8
  let mut data := a[17]!
  for (n,k) in [v[15]!,v[29]!,v[28]!].zipIdx do
    a := (((a.set! q n).set! (q+4) k).set! (q+5) (data-q*8))
    q := q+8
    data := data+n*256
  return a

def initResume (state : List Nat) (base : Nat) : Result := Id.run do
  let a := state.toArray
  if a[0]! != 1 then return fail state 14
  let stop := min a[1]! (a[2]!+4096)
  let a := (a.mapIdx fun i n => if a[2]!/8 ≤ i && i < stop/8 then 0 else n).set! 2 stop
  if stop < a[1]! then return ⟨0,1,stop,a.toList⟩
  return ⟨0,0,stop,((initHeaders a base).set! 0 2).toList⟩

end Libp2pAsm.Spec.Kernel
