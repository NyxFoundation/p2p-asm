import Libp2pAsm.Refinement.AsmBuffer.Programs
import Libp2pAsm.Refinement.AsmCodec.Programs

namespace Libp2pAsm.Refinement.AsmBuffer

open Rv64 Rv64.Logic

structure RawReference where
  slot : Word
  generation : Word
  offset : Word
  length : Word
  deriving Repr

structure RawRegion where
  generation : Word
  base : Word
  capacity : Word
  flags : Word
  deriving Repr

/-- Raw ABI decision order, including values absent from the typed SPEC domain. -/
def rawResult (table count access : Word) (ref : RawReference) (r : RawRegion) : Word × Word × Word :=
  if ¬access ≤ 1 then (4, 0, 0)
  else if count >>> (59 : Nat) ≠ 0 then (4, 0, 0)
  else if ¬ref.slot < count then (1, 0, 0)
  else if ¬table ≤ table + (ref.slot <<< (5 : Nat)) then (4, 0, 0)
  else if r.flags >>> (2 : Nat) ≠ 0 then (4, 0, 0)
  else if r.flags &&& 1 = 0 then (2, 0, 0)
  else if r.generation ≠ ref.generation then (2, 0, 0)
  else if r.capacity = 0 then (4, 0, 0)
  else if ¬r.base ≤ r.base+r.capacity then (4, 0, 0)
  else if access ≠ 0 ∧ r.flags &&& 2 = 0 then (5, 0, 0)
  else if ¬ref.length ≤ r.capacity then (3, 0, 0)
  else if ¬ref.offset ≤ r.capacity-ref.length then (3, 0, 0)
  else (0, r.base+ref.offset, ref.length)

def RawPost (result : Word × Word × Word) (s : State) : Prop :=
  AsmCodec.Output result.1 result.2.1 result.2.2 s

/-- The caller owns actual reference bytes, with no assumption on their decoded values. -/
def ReferenceAt (m : Memory) (ptr : Word) (ref : RawReference) : Prop :=
  ptr.toNat + 32 ≤ 2^64 ∧ WordAt m ptr ref.slot ∧ WordAt m (ptr+8) ref.generation ∧
    WordAt m (ptr+16) ref.offset ∧ WordAt m (ptr+24) ref.length

/-- Ownership is required only for a selected descriptor whose address arithmetic passed.
Malformed access/count and out-of-range or wrapping selection never read a descriptor. -/
def RegionAt (m : Memory) (table count access : Word) (ref : RawReference) (r : RawRegion) : Prop :=
  access ≤ 1 → count >>> (59 : Nat) = 0 → ref.slot < count →
    table ≤ table + (ref.slot <<< (5 : Nat)) →
    let ptr := table + (ref.slot <<< (5 : Nat))
    ptr.toNat + 32 ≤ 2^64 ∧ WordAt m ptr r.generation ∧ WordAt m (ptr+8) r.base ∧
      WordAt m (ptr+16) r.capacity ∧ WordAt m (ptr+24) r.flags

end Libp2pAsm.Refinement.AsmBuffer
