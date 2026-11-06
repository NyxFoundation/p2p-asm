import Libp2pAsm.Spec.Codec.QuicVarint

namespace Libp2pAsm.Spec.Quic.Wire

def maxVarint : Nat := 2^62-1

structure Error where
  code : Nat
  offset : Nat
  deriving Repr, BEq, DecidableEq

structure View where
  offset : Nat := 0
  length : Nat := 0
  deriving Repr, BEq, DecidableEq, Inhabited

def View.valid (v : View) (size : Nat) : Prop :=
  v.length ≤ size ∧ v.offset ≤ size-v.length

instance (v : View) (size : Nat) : Decidable (v.valid size) :=
  inferInstanceAs (Decidable (_ ∧ _))

structure Cursor where
  bytes : Array UInt8
  pos : Nat := 0
  deriving Repr

abbrev Parser := StateT Cursor (Except Error)

def fail (code : Nat) : Parser α := do throw ⟨code, (← get).pos⟩

def require (p : Bool) (code : Nat := 3) : Parser Unit :=
  unless p do fail code

def remaining : Parser Nat := do return (← get).bytes.size - (← get).pos

def take (n : Nat) : Parser View := do
  let s ← get
  require (s.pos ≤ s.bytes.size && n ≤ s.bytes.size-s.pos) 1
  set {s with pos := s.pos+n}
  return ⟨s.pos,n⟩

def byte : Parser Nat := do
  let v ← take 1
  return (← get).bytes[v.offset]!.toNat

def integer : Parser Nat := do
  let s ← get
  match Codec.QuicVarint.decode (s.bytes.toList.drop s.pos) with
  | .error _ => fail 1
  | .ok d =>
    let _ ← take d.consumed
    pure d.value

def bigEndian (n : Nat) : Parser Nat := do
  let v ← take n
  return ((← get).bytes.extract v.offset (v.offset+n)).foldl (fun a b => a*256+b.toNat) 0

def run (p : Parser α) (bytes : Array UInt8) : Except Error (α × Nat) := do
  let (a,s) ← p.run ⟨bytes,0⟩
  return (a,s.pos)

def viewBytes (bytes : Array UInt8) (v : View) : Except Error (List UInt8) :=
  if v.valid bytes.size then .ok ((bytes.extract v.offset (v.offset+v.length)).toList)
  else .error ⟨1,v.offset⟩

def encInt (value : Nat) : Except Error (List UInt8) :=
  (Codec.QuicVarint.encode value).mapError (fun _ => ⟨3,0⟩)

def bounded (capacity : Nat) (bytes : List UInt8) : Except Error (List UInt8) :=
  if bytes.length ≤ capacity then .ok bytes else .error ⟨5,0⟩

def packWords (words : List Nat) : List UInt8 := words.flatMap fun n =>
  (List.range 8).map fun i => (n / 256^i % 256).toUInt8

end Libp2pAsm.Spec.Quic.Wire
