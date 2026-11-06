import Libp2pAsm.Rv64.Execution

namespace Libp2pAsm.Tests.AsmCrypto

open Rv64

/-- No loaded/stored values: only control flow, access kind/width and addresses. -/
structure Event where
  pc : Word
  access : Option (Bool × Nat × Word)
  deriving BEq, Repr

def event (instruction : Instr) (s : State) : Event :=
  let access := match instruction with
    | .LD _ base offset => some (false, 8, s.getReg base + offset.signExtend 64)
    | .LBU _ base offset => some (false, 1, s.getReg base + offset.signExtend 64)
    | .SD base _ offset => some (true, 8, s.getReg base + offset.signExtend 64)
    | .SB base _ offset => some (true, 1, s.getReg base + offset.signExtend 64)
    | _ => none
  ⟨s.pc, access⟩

/-- A finite diagnostic execution, not a noninterference theorem. -/
def trace (p : Program) (count : Nat) (start : State) : Except Trap (Array Event) := do
  let (_, events) ← (List.range count).foldlM (fun (s, events) _ => do
    let instruction ← p.fetch s.pc
    let next ← execInstr instruction s
    pure (next, events.push (event instruction s))) (start, #[])
  return events

/-- Check exact owned payloads; even reads of surrounding guard bytes are rejected. -/
def footprint (rounds blockSize alignment : Nat) (e : Event) : Bool :=
  match e.access with
  | none => true
  | some (write, width, addr) =>
    let inside := fun base size => base ≤ addr.toNat && addr.toNat + width ≤ base + size
    (width == 8 && (inside 0x20008 64 || inside 0x50008 (8*rounds) || inside 0x60010 64)) ||
    (!write && ((width == 8 && inside 0x40008 (8*rounds)) ||
      (width == 1 && inside (0x30008 + alignment) blockSize)))

end Libp2pAsm.Tests.AsmCrypto
