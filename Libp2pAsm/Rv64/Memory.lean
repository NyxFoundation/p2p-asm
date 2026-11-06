import Libp2pAsm.Rv64.Basic

namespace Libp2pAsm.Rv64

structure Region where
  base : Word
  bytes : Array UInt8
  writable : Bool
  deriving Repr

def Region.endAddr (r : Region) : Nat := r.base.toNat + r.bytes.size

def Region.valid (r : Region) : Bool :=
  decide (0 < r.bytes.size ∧ r.endAddr ≤ 2 ^ 64)

def Region.disjoint (a b : Region) : Prop :=
  a.endAddr ≤ b.base.toNat ∨ b.endAddr ≤ a.base.toNat

instance (a b : Region) : Decidable (a.disjoint b) :=
  inferInstanceAs (Decidable (a.endAddr ≤ b.base.toNat ∨ b.endAddr ≤ a.base.toNat))

def Region.contains (r : Region) (width : Nat) (addr : Word) : Bool :=
  decide (r.base.toNat ≤ addr.toNat ∧ width ≤ r.bytes.size ∧
    addr.toNat - r.base.toNat ≤ r.bytes.size - width)

structure Memory where
  regions : Array Region := #[]
  deriving Repr

def Memory.valid (m : Memory) : Bool :=
  m.regions.all Region.valid && decide (m.regions.toList.Pairwise Region.disjoint)

private def supportedWidth (width : Nat) : Bool :=
  width == 1 || width == 2 || width == 4 || width == 8

private def Memory.locate (m : Memory) (width : Nat) (addr : Word) :
    Except Trap (Nat × Nat) := do
  unless m.valid do throw .invalidMemory
  unless supportedWidth width do throw .unsupportedWidth
  unless addr.toNat % width == 0 do throw .memoryMisaligned
  match m.regions.findIdx? (fun r => r.contains width addr) with
  | none => throw .memoryBounds
  | some index =>
    if h : index < m.regions.size then
      return (index, addr.toNat - m.regions[index].base.toNat)
    else throw .memoryBounds

private def readBytes (bytes : Array UInt8) (offset width : Nat) : Except Trap Word :=
  (List.range width).foldlM (fun value i =>
    if h : offset + i < bytes.size then
      .ok (value ||| (BitVec.ofNat 64 bytes[offset + i].toNat <<< (8 * i)))
    else .error .memoryBounds) 0

def Memory.load (m : Memory) (width : Nat) (addr : Word) : Except Trap Word := do
  let (index, offset) ← m.locate width addr
  if h : index < m.regions.size then
    readBytes m.regions[index].bytes offset width
  else throw .memoryBounds

private def writeBytes (bytes : Array UInt8) (offset width : Nat) (value : Word) :
    Except Trap (Array UInt8) :=
  (List.range width).foldlM (fun output i =>
    if h : offset + i < output.size then
      .ok (output.set (offset + i) ((value >>> (8 * i)).toNat.toUInt8))
    else .error .memoryBounds) bytes

def Memory.store (m : Memory) (width : Nat) (addr value : Word) : Except Trap Memory := do
  let (index, offset) ← m.locate width addr
  if h : index < m.regions.size then
    let region := m.regions[index]
    unless region.writable do throw .readOnlyMemory
    let bytes ← writeBytes region.bytes offset width value
    return { regions := m.regions.set index { region with bytes := bytes } }
  else throw .memoryBounds

end Libp2pAsm.Rv64
