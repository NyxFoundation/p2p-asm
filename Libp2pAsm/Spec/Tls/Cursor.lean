import Libp2pAsm.Spec.Tls.Basic

namespace Libp2pAsm.Spec.Tls

structure Cursor where
  input : Bytes
  pos : Nat
  stop : Nat
  deriving Repr

def Cursor.valid (c : Cursor) : Prop := c.pos ≤ c.stop ∧ c.stop ≤ c.input.size

/-- Bounds use subtraction only after checking the cursor invariant. -/
def Cursor.take (c : Cursor) (n : Nat) : Except Error (Slice × Cursor) := do
  if c.pos > c.stop || c.stop > c.input.size || n > c.stop-c.pos then throw .malformed
  return (⟨c.pos,n⟩, {c with pos := c.pos+n})

def Cursor.uint (c : Cursor) (width : Nat) : Except Error (Nat × Cursor) := do
  if width == 0 || width > 4 then throw .malformed
  let (s,next) ← c.take width
  return ((s.bytes c.input).foldl (fun n b => 256*n+b.toNat) 0, next)

def Cursor.vector (c : Cursor) (width minimum : Nat) : Except Error (Slice × Cursor) := do
  let (n,c) ← c.uint width
  if n < minimum then throw .malformed
  c.take n

def Cursor.done (c : Cursor) : Except Error Unit := do
  if c.pos != c.stop then throw .malformed

def Cursor.sub (c : Cursor) (s : Slice) : Cursor := ⟨c.input,s.offset,s.offset+s.length⟩

def frame (input : Bytes) (limit : Nat) : Except Error (Nat × Cursor) := do
  if input.size < 4 then throw .needMore
  let (kind,c) ← (Cursor.mk input 0 input.size).uint 1
  let (length,c) ← c.uint 3
  if length > limit then throw .limit
  if input.size-4 < length then throw .needMore
  return (kind, {c with stop := 4+length})

/-- All prefix lengths are checked before truncating to their protocol width. -/
def vector (width minimum : Nat) (payload : Bytes) : Except Error Bytes := do
  if width == 0 || width > 3 then throw .malformed
  if payload.size < minimum || payload.size ≥ 256^width then throw .malformed
  return be width payload.size ++ payload

end Libp2pAsm.Spec.Tls
