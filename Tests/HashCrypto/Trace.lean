import Tests.HashCrypto.Support

namespace Libp2pAsm.Tests.HashCrypto
open Rv64

/-- Check only public PC and read/write kind, width and address, never loaded data. -/
def permitted (c : Case) (e : AsmCrypto.Event) : Bool := match e.access with
  | none => true
  | some (write, width, addr) =>
    let inside := fun base size => base ≤ addr.toNat && addr.toNat+width ≤ base+size
    let align := c.field 5
    (!write && (inside (0x100008+align) c.a.size || inside (0x200008+align) c.b.size ||
      inside 0x500008 (if ((c.start.memory.regions[4]?).getD (⟨0, #[], false⟩ : Region)).bytes.size == 656 then 640 else 512) ||
      inside 0x6001a0 8)) ||
    inside (0x300008+align) (((c.start.memory.regions[2]?).getD (⟨0, #[], false⟩ : Region)).bytes.size-16-align) ||
    inside 0x400008 (c.field 1) || inside (0x6001a0-c.field 2) (c.field 2)

def changed (c : Case) : Case :=
  let flip := fun (bs : Array UInt8) => bs.map (· ^^^ 0xff)
  let a := flip c.a
  let b := flip c.b
  let regions := c.start.memory.regions.mapIdx fun i r =>
    if i == 0 then { r with bytes := replaced r.bytes (8+c.field 5) a }
    else if i == 1 then { r with bytes := replaced r.bytes (8+c.field 5) b } else r
  { c with a := a, b := b, start := { c.start with memory := ⟨regions⟩ } }

/-- Finite lockstep trace comparison; this is NOT a constant-time proof. -/
def tracePair (p : Program) (c : Case) : Nat → State → State → Except String State
  | 0, a, b => if a.pc == 0x80000 && b.pc == 0x80000 then .ok b else .error "trace fuel"
  | n+1, a, b => do
    let ia ← (p.fetch a.pc).mapError reprStr
    let ib ← (p.fetch b.pc).mapError reprStr
    let ea := AsmCrypto.event ia a
    let eb := AsmCrypto.event ib b
    unless ea == eb && permitted c ea do throw s!"trace/footprint at {repr ea}"
    tracePair p c n (← (execInstr ia a).mapError reprStr) (← (execInstr ib b).mapError reprStr)

end Libp2pAsm.Tests.HashCrypto
